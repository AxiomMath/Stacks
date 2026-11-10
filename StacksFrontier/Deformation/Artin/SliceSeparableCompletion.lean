module

public import StacksFrontier.Deformation.Artin.SliceProrepresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparablePoint
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Height

/-!
# Prorepresenting the deformations of a point of a scheme over a separable extension

Let `v₀ : Spec k ⟶ V` be a point of a scheme `V` locally of finite type over `S`, with `k` finite
over `Λ`, and let `c` be an affine chart `Spec R ⊆ V` at its image point. The kernel `𝔭` of the
ring map `R ⟶ k` of `v₀` is maximal, because `k` is integral over `R`. If `k` is separable over
a field `l` whose image in `k` lies in the image of `R` (so `k` is separable over `R/𝔭`), then the
deformation category of `v₀` is prorepresented over `𝒞_Λ` by a Noetherian complete local
`Λ`-algebra of the dimension of `R_𝔭`, which is the dimension of the local ring of `V` at the
image point.

## Main results

* `AlgHom.isMaximal_ker_of_finite`: the kernel of an algebra map to a field finite over the base
  is maximal.
* `Deformation.Artin.SliceTangent.exists_sliceEquivalence_of_isSeparable`: the deformation
  category of `v₀` is prorepresented by a Noetherian complete local `Λ`-algebra of the dimension of
  `R_𝔭`.
* `Deformation.Artin.SliceTangent.ringKrullDim_stalk_eq_localization`: the dimension of the local
  ring of `V` at the image point is the dimension of `R_𝔭`.
* `Deformation.Artin.SliceTangent.exists_affineChart_comp`: an affine chart of the target of a
  morphism at the image of a point contains in its preimage an affine chart of the source at it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The kernel of an algebra map to a field which is finite over the base is maximal. -/
theorem AlgHom.isMaximal_ker_of_finite {Λ R L : Type*} [CommRing Λ] [CommRing R] [Field L]
    [Algebra Λ R] [Algebra Λ L] [Module.Finite Λ L] (φ : R →ₐ[Λ] L) :
    (RingHom.ker φ.toRingHom).IsMaximal := by
  let : Algebra R L := φ.toRingHom.toAlgebra
  have : IsScalarTower Λ R L := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Algebra.IsIntegral R L := Algebra.IsIntegral.tower_top Λ
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal L)

/-- The dimensions of the localizations of a ring at two equal prime ideals are equal. -/
theorem ringKrullDim_localization_congr {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J)
    [I.IsPrime] [J.IsPrime] :
    ringKrullDim (Localization.AtPrime I) = ringKrullDim (Localization.AtPrime J) := by
  subst h; rfl

namespace Deformation.Artin.SliceTangent

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V : BigFppfOver B S hS}
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
variable {v₀ : Over V}
variable {hv₀ : (Over.forget V ⋙ Over.post B.inclusion).obj v₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
variable [IsOpenImmersion iΛ] (c : AffineChart iΛ (B.inclusion.map V.hom)
  ((pointMap hv₀).base (closedPt (.of k))))

attribute [local instance] chartAlgebra

/-- The ring map of the point of the chart, as a map of `Λ`-algebras. -/
noncomputable def pointValueAlgHom : c.ring →ₐ[Λ] k :=
  { (pointValue c).hom with
    commutes' := fun r => by
      have h := c.structureMap_ringMap (CommRingCat.ofHom (algebraMap Λ k)) (pointMap hv₀)
        (range_pointMap c) pointMap_comp
      exact congrArg (fun f : CommRingCat.of Λ ⟶ CommRingCat.of k => f.hom r) h }

/-- The underlying ring map of `pointValueAlgHom c` is that of `pointValue c`. -/
theorem pointValueAlgHom_toRingHom : (pointValueAlgHom c).toRingHom = (pointValue c).hom := rfl

/-- **The deformations of a point of a scheme are prorepresented over a separable extension of a
subfield of the chart residue field.** Let `l` be a field mapping into `k`, separably, with image
inside the image of the chart ring. Then the deformation category of `v₀` is equivalent over `𝒞_Λ`
to `A|_{𝒞_Λ}` for a Noetherian complete local `Λ`-algebra `A` with residue field `k` of the
dimension of the localization of the chart ring at the kernel of its map to `k`. -/
theorem exists_sliceEquivalence_of_isSeparable [IsNoetherianRing Λ] [Module.Finite Λ k]
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {l : Type u} [Field l] [Algebra l k] [Algebra.IsSeparable l k]
    (hl : ∀ x : l, ∃ r : c.ring, (pointValue c).hom r = algebraMap l k x) :
    letI : (RingHom.ker (pointValue c).hom).IsPrime :=
      (pointValueAlgHom c).isMaximal_ker_of_finite.isPrime
    ∃ A : CompleteLocalAlgCat.{u, u, u} Λ k,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (Functor.Elements.π (restrictedCoyoneda A)) (sliceDeformations iΛ v₀ hv₀).projection) ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (RingHom.ker (pointValue c).hom)) := by
  let φ := pointValueAlgHom c
  let P := RingHom.ker φ.toRingHom
  have hP : P.IsMaximal := φ.isMaximal_ker_of_finite
  let : Field (c.ring ⧸ P) := Ideal.Quotient.field P
  let K := c.ring ⧸ P
  let ψ : K →ₐ[Λ] k := Ideal.Quotient.liftₐ P φ (fun a ha => (RingHom.mem_ker).1 ha)
  let : Algebra K k := ψ.toRingHom.toAlgebra
  have : IsScalarTower Λ K k := IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  have : Module.Finite Λ K := Module.Finite.of_injective ψ.toLinearMap hψinj
  have : Module.Finite K k := Module.Finite.of_restrictScalars_finite Λ K k
  have hrange : ∀ x : l, algebraMap l k x ∈ ψ.toRingHom.range := by
    intro x
    obtain ⟨r, hr⟩ := hl x
    exact ⟨Ideal.Quotient.mk P r, hr⟩
  let e : K ≃+* ψ.toRingHom.range :=
    RingEquiv.ofBijective ψ.toRingHom.rangeRestrict
      ⟨fun a b h => hψinj (congrArg Subtype.val h), ψ.toRingHom.rangeRestrict_surjective⟩
  let ι : l →+* K := e.symm.toRingHom.comp ((algebraMap l k).codRestrict _ hrange)
  have hι : ψ.toRingHom.comp ι = (algebraMap l k).comp (RingHom.id l) := by
    ext x
    change ψ (e.symm ⟨algebraMap l k x, hrange x⟩) = algebraMap l k x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨algebraMap l k x, hrange x⟩)
  have : Algebra.IsSeparable K k :=
    Algebra.isSeparable_of_comp_eq_comp_of_bijective (RingHom.id l) Function.bijective_id ι
      ψ.toRingHom hι
  let q : c.ring →ₐ[Λ] K := Ideal.Quotient.mkₐ Λ P
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective Λ P
  have hχ : ∀ r : c.ring, algebraMap K k (q r) = (pointValue c).hom r := fun r => rfl
  obtain ⟨A, hA, hdim⟩ := exists_sliceEquivalence_completion (K := K) c hfin hqc q hq hχ
  exact ⟨A, hA, hdim.trans
    (@ringKrullDim_localization_congr _ _ _ _ Ideal.mk_ker (RingHom.ker_isPrime _) _)⟩

/-- **The dimension of the local ring of a scheme at the image of a point of a chart** is the
dimension of the localization of the chart ring at the kernel of its map to the field. -/
theorem ringKrullDim_stalk_eq_localization [Module.Finite Λ k] :
    letI : (RingHom.ker (pointValue c).hom).IsPrime :=
      (pointValueAlgHom c).isMaximal_ker_of_finite.isPrime
    ringKrullDim ((B.inclusion.obj V.left).presheaf.stalk ((pointMap hv₀).base (closedPt (.of k))))
      = ringKrullDim (Localization.AtPrime (RingHom.ker (pointValue c).hom)) := by
  let : (RingHom.ker (pointValue c).hom).IsPrime :=
    (pointValueAlgHom c).isMaximal_ker_of_finite.isPrime
  let x : c.U := ⟨(pointMap hv₀).base (closedPt (.of k)), c.mem⟩
  have hx : (c.isAffineOpen.primeIdealOf x).asIdeal = RingHom.ker (pointValue c).hom := by
    have h1 := c.isAffineOpen.fromSpec_primeIdealOf x
    have h2 : (pointMap hv₀).base (closedPt (.of k)) =
        c.fromSpec.base ((Spec.map (pointValue c)).base (closedPt (.of k))) := by
      rw [← Scheme.Hom.comp_apply, c.spec_ringMap]
    have hinj : Function.Injective c.fromSpec.base := c.fromSpec.isOpenEmbedding.injective
    have h3 : c.isAffineOpen.primeIdealOf x = (Spec.map (pointValue c)).base (closedPt (.of k)) :=
      hinj (h1.trans h2)
    rw [h3]
    ext r
    change r ∈ Ideal.comap (pointValue c).hom (IsLocalRing.maximalIdeal k) ↔ _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  let := TopCat.Presheaf.algebra_section_stalk (B.inclusion.obj V.left).presheaf x
  have := c.isAffineOpen.isLocalization_stalk x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (c.isAffineOpen.primeIdealOf x).asIdeal
    ((B.inclusion.obj V.left).presheaf.stalk x.1),
    IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker (pointValue c).hom)
    (Localization.AtPrime (RingHom.ker (pointValue c).hom))]
  congr 1
  exact congrArg Ideal.height hx ▸ rfl

section ChartComp

variable {Y Z : Scheme.{u}} {s : Y ⟶ S} {s' : Z ⟶ S}

omit [IsOpenImmersion iΛ] in
/-- **An affine chart of the source of a morphism inside the preimage of a chart of the
target.** For `f : Z ⟶ Y` over `S` and a field-valued point `pt` of `Z`, an affine chart `c` of `Y`
at the image of `pt` has inside its preimage an affine chart `c'` of `Z` at `pt`, and the ring map
of `pt ≫ f` out of `c` factors through that of `pt` out of `c'`. -/
theorem exists_affineChart_comp (f : Z ⟶ Y) (hf : f ≫ s = s') {K : Type u} [Field K]
    (pt : Spec (.of K) ⟶ Z) (c : AffineChart iΛ s ((pt ≫ f).base (closedPt (.of K))))
    (hpt : Set.range (pt ≫ f).base ⊆ c.U) :
    ∃ (c' : AffineChart iΛ s' (pt.base (closedPt (.of K))))
      (hpt' : Set.range pt.base ⊆ c'.U) (ρ : c.ring ⟶ c'.ring),
      c.ringMap (pt ≫ f) hpt = ρ ≫ c'.ringMap pt hpt' := by
  let O : Z.Opens := f ⁻¹ᵁ c.U
  have hO : pt.base (closedPt (.of K)) ∈ O := c.mem
  obtain ⟨U', hU', hy, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Scheme.isBasis_affineOpens Z)) hO
  let c' : AffineChart iΛ s' (pt.base (closedPt (.of K))) :=
    ⟨U', hU', hy, fun z hz => by
      change s'.base z ∈ Set.range iΛ.base
      rw [← hf]
      exact c.le (hle hz)⟩
  have hpt' : Set.range pt.base ⊆ c'.U := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (closedPt (.of K))]
    exact c'.mem
  have hg : Set.range (c'.fromSpec ≫ f).base ⊆ c.U := by
    rintro _ ⟨z, rfl⟩
    have hz : c'.fromSpec.base z ∈ (c'.U : Set Z) := by
      rw [← c'.isAffineOpen.range_fromSpec]; exact ⟨z, rfl⟩
    exact hle hz
  refine ⟨c', hpt', c.ringMap (c'.fromSpec ≫ f) hg, ?_⟩
  have hfac : pt ≫ f = Spec.map (c'.ringMap pt hpt') ≫ (c'.fromSpec ≫ f) := by
    rw [← Category.assoc, c'.spec_ringMap]
  rw [c.ringMap_congr hpt (hfac ▸ hpt) hfac, c.ringMap_comp]

end ChartComp

end Deformation.Artin.SliceTangent

end
