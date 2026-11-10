module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.JacobianOfPicardZero
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Pic⁰` of a curve over an arbitrary field is an abelian variety

Let `X` be a proper smooth geometrically irreducible curve over a field `K` with a rational
point `σ`, and let `A` be a smooth group scheme over `K` representing the degree-zero rigidified
Picard functor `Pic⁰_{X/K,σ}`. Then `A` is an abelian variety. No hypothesis on `K` is needed; in
particular this covers the separably closed fields of [Stacks, Tag 0BA0].

## Main results

* `Stacks.Hilbert.exists_familyOfPoints_eq_of_isAlgClosed`: a Hilbert family over the spectrum of
  an algebraically closed field is a sum of points.
* `AlgebraicGeometry.exists_algebraicClosure_point_of_isClosed`: a closed point of a scheme
  locally of finite type over `K` is the image of a `K̄`-point.
* `AlgebraicGeometry.isAbelianVariety_of_closedPoints_subset_range`: a smooth group scheme over
  `K` onto whose closed points a connected proper scheme maps is an abelian variety.
* `Stacks.RigidifiedPicard.exists_comp_abelPowerHom_eq_of_isAlgClosed`: every `K̄`-point of `A`
  comes from a `K̄`-point of `X^n` under the Abel morphism, for `n` at least the genus of `X_{K̄}`.
* `Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero_field`: **the conclusion**.
* `Stacks.WeilCohomology.jacobianParametrization_of_iso_functorZero_field`: the Jacobian input
  of the curve case of [Stacks, Tag 0FH7] over an arbitrary field.

## Implementation notes

The argument of `Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero` over an
algebraically closed field runs through rational points of `A`; here it runs through `K̄`-points,
so neither a descent nor a base change of `A` is needed. The representation of `Pic⁰` gives the
class of a `K̄`-point of `A` directly on `X_{K̄}`, where Riemann-Roch and the decomposition of
divisors into points apply, and closed points of `A` are images of `K̄`-points.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Hilbert

/-- **A Hilbert family over an algebraically closed field point is a sum of points.** Let `X`
be a separated scheme smooth of relative dimension one over a base `S`, and let `T` be an
`S`-scheme whose underlying scheme is the spectrum of an algebraically closed field `Ω`. Every
degree-`d` Hilbert family of `X` over `T` is the sum `[x₁] + ⋯ + [x_d]` of `d` points
`T ⟶ X`. -/
theorem exists_familyOfPoints_eq_of_isAlgClosed {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (g : Spec (.of Ω) ⟶ S) :
    ∀ (d : ℕ) (Z : HilbertFamily X (Over.mk g) d),
      ∃ x : Fin d → (Over.mk g ⟶ X), familyOfPoints X (Over.mk g) x = Z := by
  have := SmoothOfRelativeDimension.smooth 1 X.hom
  intro d
  induction d with
  | zero =>
    intro Z
    refine ⟨Fin.elim0, HilbertFamily.ext ?_⟩
    rw [Z.ideal_eq_top]
    exact HilbertFamily.ideal_eq_top _
  | succ d ih =>
    intro Z
    set B := ((Over.pullback (Over.mk g).hom).obj X).left
    set q : B ⟶ Spec (.of Ω) := pullback.snd X.hom g
    have hq : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom g))
    have h1 := Z.isFiniteLocallyFreeOfRank
    obtain ⟨hfin, hflat, -⟩ :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        (Z.ideal.subschemeι ≫ ((Over.pullback (Over.mk g).hom).obj X).hom)).mp
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (d + 1))
    have hne : Nonempty Z.ideal.subscheme := by
      by_contra hcon
      have : IsEmpty Z.ideal.subscheme := not_nonempty_iff.mp hcon
      have h0 := Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty_source
        (Z.ideal.subschemeι ≫ ((Over.pullback (Over.mk g).hom).obj X).hom)
      have : Flat (Z.ideal.subschemeι ≫ ((Over.pullback (Over.mk g).hom).obj X).hom) := hflat
      obtain ⟨s⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
      have e0 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ 0).mp h0 s
      have e1 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mp h1 s
      omega
    have : JacobsonSpace (Over.mk g).left := inferInstanceAs (JacobsonSpace (Spec (.of Ω)))
    have := LocallyOfFiniteType.jacobsonSpace
      (Z.ideal.subschemeι ≫ ((Over.pullback (Over.mk g).hom).obj X).hom)
    obtain ⟨w, -, hw⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set Z.ideal.subscheme))
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    set z := Z.ideal.subschemeι w
    have hz : IsClosed {z} := by
      simpa [Set.image_singleton] using Z.ideal.subschemeι.isClosedEmbedding.isClosedMap _ hw
    set w' := pointOfClosedPoint q z hz
    have hw'q : w' ≫ q = 𝟙 _ := pointOfClosedPoint_comp _ _ _
    let x₀ : Over.mk g ⟶ X := Over.homMk (w' ≫ pullback.fst X.hom g) (by
      change (w' ≫ pullback.fst X.hom g) ≫ X.hom = g
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (w' ≫ q) ≫ g = g
      rw [hw'q, Category.id_comp])
    have hgraph_eq : pointGraph X (Over.mk g) x₀ = w' := by
      refine pullback.hom_ext (pullback.lift_fst _ _ _) ?_
      rw [pointGraph, pullback.lift_snd]
      exact hw'q.symm
    have hgraph : Set.range (pointGraph X (Over.mk g) x₀) ⊆ (Z.ideal.support : Set B) := by
      rintro _ ⟨t, rfl⟩
      rw [hgraph_eq, pointOfClosedPoint_apply, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    have : IsReduced (Over.mk g).left := inferInstanceAs (IsReduced (Spec (.of Ω)))
    obtain ⟨g', hg'⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
      Z.ideal (pointGraph X (Over.mk g) x₀)).2 hgraph
    have hle : Z.ideal ≤ pointIdeal X (Over.mk g) x₀ := by
      rw [pointIdeal, ← hg']
      exact Z.ideal.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp _ _)
    obtain ⟨D', hD'⟩ := exists_familyAddPoint_eq Z x₀ hle
    obtain ⟨x', hx'⟩ := ih D'
    refine ⟨Fin.cons x₀ x', HilbertFamily.ext ?_⟩
    rw [familyOfPoints_ideal, Fin.prod_univ_succ, Fin.cons_zero, hD', ← hx',
      familyOfPoints_ideal, mul_comm]
    simp only [Fin.cons_succ]

end Stacks.Hilbert

namespace AlgebraicGeometry

/-- **A closed point of a scheme locally of finite type over a field is the image of a geometric
point over the algebraic closure.** If `q : Y ⟶ Spec K` is locally of finite type and `y` is a
closed point of `Y`, there is a morphism `b : Spec K̄ ⟶ Y` over `Spec K` whose image is `y`:
the residue field `κ(y)` is finite over `K`, so it embeds into `K̄` over `K`. -/
theorem exists_algebraicClosure_point_of_isClosed {K : Type u} [Field K] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of K)) [LocallyOfFiniteType q] (y : Y) (hy : IsClosed {y}) :
    ∃ b : Spec (.of (AlgebraicClosure K)) ⟶ Y,
      b ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ∧
        y ∈ Set.range b := by
  have hfin : IsFinite (Y.fromSpecResidueField y ≫ q) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hy
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  set ψ : CommRingCat.of K ⟶ Y.residueField y := Spec.preimage (Y.fromSpecResidueField y ≫ q)
  have hψ : Spec.map ψ = Y.fromSpecResidueField y ≫ q := Spec.map_preimage _
  have hint : ψ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hψ]
    infer_instance
  let : Algebra K (Y.residueField y) := ψ.hom.toAlgebra
  have : Algebra.IsIntegral K (Y.residueField y) := ⟨hint⟩
  let emb : Y.residueField y →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ Y.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext x
    exact emb.commutes x
  · obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (.of (AlgebraicClosure K))))
    exact ⟨p, by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

/-- **A morphism from a universally closed scheme whose image contains every closed point is
surjective**, when the target is separated and locally of finite type over a field: the image is
closed and the target is a Jacobson space. -/
theorem surjective_of_closedPoints_subset_range {K : Type u} [Field K] {Y A : Scheme.{u}}
    (p : Y ⟶ Spec (.of K)) (q : A ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated q]
    [LocallyOfFiniteType q] (α : Y ⟶ A) (hα : α ≫ q = p)
    (h : ∀ a : A, IsClosed {a} → a ∈ Set.range α) : Surjective α := by
  have : UniversallyClosed (α ≫ q) := hα ▸ inferInstance
  have : UniversallyClosed α := UniversallyClosed.of_comp_of_isSeparated α q
  have := LocallyOfFiniteType.jacobsonSpace q
  have hclosed : IsClosed (Set.range α) := α.isClosedMap.isClosed_range
  refine ⟨fun x => ?_⟩
  by_contra hx
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.range α)ᶜ) ⟨x, hx⟩
    hclosed.isOpen_compl.isLocallyClosed
  exact hz (h z hzc)

/-- **A smooth group scheme over a field covered on closed points by a connected proper scheme
is an abelian variety.** -/
theorem isAbelianVariety_of_closedPoints_subset_range {K : Type u} [Field K]
    (A : Grp (Over (Spec (.of K)))) [Smooth A.X.hom] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    [IsProper p] [ConnectedSpace Y] (α : Y ⟶ A.X.left) (hα : α ≫ A.X.hom = p)
    (h : ∀ a : A.X.left, IsClosed {a} → a ∈ Set.range α) :
    IsAbelianVariety K A.X := by
  have : IsSeparated A.X.hom := by
    let : GrpObj (Over.mk A.X.hom) :=
      GrpObj.ofIso (show A.X ≅ Over.mk A.X.hom from Over.isoMk (Iso.refl _))
    exact (isSeparated_iff_isClosedImmersion_one A.X.hom).2 inferInstance
  have hs := surjective_of_closedPoints_subset_range p A.X.hom α hα h
  have : UniversallyClosed (α ≫ A.X.hom) := hα ▸ inferInstance
  have : UniversallyClosed A.X.hom := UniversallyClosed.of_comp_surjective α A.X.hom
  have : CompactSpace Y := (quasiCompact_iff_compactSpace p).1 inferInstance
  have : CompactSpace A.X.left := hs.surj.compactSpace α.continuous
  have : QuasiCompact A.X.hom := (quasiCompact_iff_compactSpace A.X.hom).2 inferInstance
  have : IsProper A.X.hom := ⟨⟩
  have : ConnectedSpace A.X.left := hs.surj.connectedSpace α.continuous
  have : GeometricallyReduced A.X.hom := geometricallyReduced_of_smooth A.X.hom
  exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced K A.X

end AlgebraicGeometry

namespace Stacks.RigidifiedPicard

/-- The projection of the base change of a smooth geometrically irreducible curve is
geometrically integral. -/
private theorem geometricallyIntegral_bcProj {K Ω : Type u} [Field K] [Field Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIrreducible f]
    (g : Spec (.of Ω) ⟶ Spec (.of K)) : GeometricallyIntegral (bcProj f (Over.mk g)) := by
  have := geometricallyIntegral_of_smooth f
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd f g))

section Field

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsProper f] [SmoothOfRelativeDimension 1 f]
  (hdim : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  {A : Grp (Over (Spec (.of K)))} (e : CategoryTheory.yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- **The Abel morphism hits every point over an algebraically closed field.** Let `Ω` be an
algebraically closed field with a morphism `g : Spec Ω ⟶ Spec K`, and let `n` be at least the
genus of `X_Ω`. Every `Ω`-point of `A` over `K` is the image under the Abel morphism `X^n ⟶ A` of
an `Ω`-point of `X^n`: it classifies a class `c` of degree zero on `X_Ω`, Riemann-Roch writes
`c + n[σ]` as the class of an effective divisor of degree `n`, and that divisor is a sum of `n`
points over `Ω` because `Ω` is algebraically closed. -/
theorem exists_comp_abelPowerHom_eq_of_isAlgClosed {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (g : Spec (.of Ω) ⟶ Spec (.of K)) [IsIntegral (bc f (Over.mk g))]
    [IsIso ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (bcProj f (Over.mk g)).appTop)]
    (hdim₀ : topologicalKrullDim (bc f (Over.mk g)) ≤ 1) (n : ℕ)
    (hn : genus (bcProj f (Over.mk g)) ≤ n) (b : Over.mk g ⟶ A.X) :
    ∃ y : Over.mk g ⟶ fibrePower f n, y ≫ abelPowerHom f hdim σ hσ e n = b := by
  have : Subsingleton (Over.mk g).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  have : Nonempty (Over.mk g).left := inferInstanceAs (Nonempty (Spec (.of Ω)))
  set π₀ : bc f (Over.mk g) ⟶ Spec (.of Ω) := bcProj f (Over.mk g)
  have hdim' := topologicalKrullDim_fiber_bcProj_le f hdim (Over.mk g)
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  set c := representedClass f hdim σ hσ e b
  have hc : invertibleCurveDegreeHom Ω π₀ hdim₀ c = 0 := by
    obtain ⟨x, hx, hxc⟩ := representedClass_mem_groupZero f hdim σ hσ e b
    have h := (mem_groupZero_iff f hdim σ hσ (Over.mk g) x).1 hx t
    rwa [degree_apply, hxc,
      relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom π₀ hdim' hdim₀] at h
  set E : Stacks.Picard.ofScheme (bc f (Over.mk g)) :=
    Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) (Over.mk g)
      fun _ : Fin n => sectionPoint f σ hσ (Over.mk g))
  have hE : invertibleCurveDegreeHom Ω π₀ hdim₀ E = n := by
    rw [← relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom π₀ hdim' hdim₀ t]
    exact relativeInvertibleDegreeHomAt_abelClass_familyOfPoints f hdim (Over.mk g) _ t
  have hdeg : (genus π₀ : ℤ) ≤ invertibleCurveDegreeHom Ω π₀ hdim₀ (c + E) := by
    rw [map_add, hc, hE, zero_add]
    exact_mod_cast hn
  obtain ⟨D, hD, d, hrank, hd, hclass⟩ :=
    exists_isEffectiveCartierDivisor_picardClass_eq Ω π₀ hdim₀ (c + E) hdeg
  have hdn : d = n := by
    rw [map_add, hc, hE, zero_add] at hd
    exact_mod_cast hd
  let Z : Stacks.Hilbert.HilbertFamily (Over.mk f) (Over.mk g) n := ⟨D, hdn ▸ hrank⟩
  obtain ⟨x, hx⟩ := Stacks.Hilbert.exists_familyOfPoints_eq_of_isAlgClosed (Over.mk f) g n Z
  refine ⟨Pi.lift x, (representedClass_injective f hdim σ hσ e (Over.mk g)) ?_⟩
  rw [representedClass_comp, abelPowerHom, representedClass_classifyingHom,
    AddEquiv.apply_symm_apply, schemePullbackClass_bcMap_abelPowerClass f σ hσ n]
  simp only [Pi.lift_comp_π]
  rw [hx, show Stacks.Hilbert.abelClass Z = c + E from hclass]
  exact add_sub_cancel_right c E

omit [IsProper f] [SmoothOfRelativeDimension 1 f] in
/-- The base change of a smooth geometrically irreducible curve to a field is integral. -/
theorem isIntegral_bc_spec [Smooth f] [GeometricallyIrreducible f] {Ω : Type u} [Field Ω]
    (g : Spec (.of Ω) ⟶ Spec (.of K)) : IsIntegral (bc f (Over.mk g)) := by
  have := geometricallyIntegral_bcProj f g
  have : Subsingleton (Over.mk g).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  have : IsIntegral (Over.mk g).left := inferInstanceAs (IsIntegral (Spec (.of Ω)))
  exact GeometricallyIntegral.isIntegral_of_subsingleton (bcProj f (Over.mk g))

omit [SmoothOfRelativeDimension 1 f] in
/-- The global functions on the base change of a proper smooth geometrically irreducible curve
to a field are the constants (Tag 0BUG). -/
theorem isIso_globalSections_bc_spec [Smooth f] [GeometricallyIrreducible f] {Ω : Type u}
    [Field Ω] (g : Spec (.of Ω) ⟶ Spec (.of K)) :
    IsIso ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (bcProj f (Over.mk g)).appTop) := by
  have := geometricallyIntegral_bcProj f g
  exact isIso_globalSections_of_geometricallyIntegral Ω _

include e in
/-- **`Pic⁰` of a smooth proper curve over a field is an abelian variety.** Let `X` be a proper
smooth geometrically irreducible curve over a field `K` with a rational point `σ`, and let `A` be
a group scheme over `K`, smooth over `K`, representing the degree-zero rigidified Picard functor
`Pic⁰_{X/K,σ}`. Then `A` is an abelian variety.

With `n` the genus of `X_{K̄}`, the Abel morphism `X^n ⟶ A` is proper because `X^n` is proper and
`A` separated, and its image contains every closed point of `A`: such a point is the image of a
`K̄`-point of `A` (`AlgebraicGeometry.exists_algebraicClosure_point_of_isClosed`), and every
`K̄`-point of `A` comes from a `K̄`-point of `X^n` by Riemann-Roch on `X_{K̄}`
(`exists_comp_abelPowerHom_eq_of_isAlgClosed`). So `A` is the image of the connected proper
scheme `X^n`, hence proper and connected, and it is geometrically reduced because it is
smooth. -/
@[sga "6 XII 1.2" "special case", sga "7 IX 12.1.11" "partial"]
theorem isAbelianVariety_of_iso_functorZero_field [Smooth f] [GeometricallyIrreducible f]
    (hdimX : topologicalKrullDim X ≤ 1) [Smooth A.X.hom] :
    AlgebraicGeometry.IsAbelianVariety K A.X := by
  set g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have := isIntegral_bc_spec f g
  have := isIso_globalSections_bc_spec f g
  have hdim₀ : topologicalKrullDim (bc f (Over.mk g)) ≤ 1 :=
    (topologicalKrullDim_baseChange K (AlgebraicClosure K) (pullback.fst f g) (pullback.snd f g) f
      (IsPullback.of_hasPullback f g)).trans_le hdimX
  set n := genus (bcProj f (Over.mk g))
  have : IsProper (fibrePower f n).hom :=
    @isProper_fibrePower_hom _ _ (inferInstanceAs (IsProper f)) n
  have : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  have : GeometricallyIrreducible (Over.mk f).hom := inferInstanceAs (GeometricallyIrreducible f)
  have : IsIntegral (fibrePower f n).left := Stacks.Scheme.isIntegral_fibrePower (Over.mk f) n
  refine isAbelianVariety_of_closedPoints_subset_range A (fibrePower f n).hom
    (abelPowerHom f hdim σ hσ e n).left (Over.w _) fun a ha => ?_
  obtain ⟨b, hb, p, rfl⟩ := exists_algebraicClosure_point_of_isClosed A.X.hom a ha
  obtain ⟨y, hy⟩ := exists_comp_abelPowerHom_eq_of_isAlgClosed f hdim σ hσ e g hdim₀ n le_rfl
    (Over.homMk b hb)
  refine ⟨y.left p, ?_⟩
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, Over.homMk_left] using
    congrArg (fun m => m.left p) hy

end Field

end Stacks.RigidifiedPicard

namespace Stacks.WeilCohomology

/-- **The Jacobian parametrization over an arbitrary field, from a representation of `Pic⁰`.**
The variant of `Stacks.WeilCohomology.jacobianParametrization_of_iso_functorZero` with no
hypothesis on the ground field `K`: `A` is an abelian variety by
`Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero_field`, and the classes of its
rational points are exactly the degree-zero Picard classes of `X`, with multiplication by `n` on
`A` becoming multiplication by `n`. -/
theorem jacobianParametrization_of_iso_functorZero_field {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [SmoothOfRelativeDimension 1 f] (hdimX : topologicalKrullDim X ≤ 1)
    (hdim : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (A : Grp (Over (Spec (.of K)))) [Smooth A.X.hom]
    (e : CategoryTheory.yonedaGrp.obj A ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
    (n : ℤ) :
    JacobianParametrization K n f hdimX :=
  ⟨A, Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero_field f hdim σ hσ e hdimX,
    Stacks.RigidifiedPicard.pointClass f hdim σ hσ e,
    fun c hc => Stacks.RigidifiedPicard.exists_pointClass_eq f hdimX hdim σ hσ e c hc,
    fun g g' hg hg' h => Stacks.RigidifiedPicard.pointClass_eq_zsmul f hdim σ hσ e n g g' hg hg' h⟩

end Stacks.WeilCohomology
