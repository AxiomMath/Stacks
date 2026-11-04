module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.FiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import
  StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.OrbitDecomposition
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed

/-!
# Invertible functions on a connected reduced scheme over an arbitrary field

Let `k` be a field and let `X` be a scheme over `k` which is locally of finite type, connected,
reduced and has finitely many irreducible components.  Stacks Tag 04L7 says that the group
`𝒪(X)^*/k^*` of invertible global functions modulo the constants is a finitely generated abelian
group as soon as one of

1. the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`,
2. `X` has a `k`-rational point, or
3. `X` is geometrically integral

holds.  This file proves it under (1), and under (2) by way of the source's reduction of (2)
to (1).  Condition (3) is treated in
`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/ConnectedReducedGeometricallyIntegral.lean`,
which reduces it to (1) as well; the source omits that verification.

## Main results

* `AlgebraicGeometry.mem_range_of_isIntegralElem_of_rationalPoint`: **(2) implies (1).** If `X`
  has a `k`-rational point then every global section integral over `k` is a constant.
* `AlgebraicGeometry.mem_range_of_isIntegralElem_of_isAlgClosed`: over an algebraically closed
  base field, condition (1) is automatic.
* `AlgebraicGeometry.fg_units_quotient_of_integrallyClosed`: **Tag 04L7 under condition (1)**.
* `AlgebraicGeometry.fg_units_quotient_of_rationalPoint`: **Tag 04L7 under condition (2)**.

## Implementation notes

Condition (1), "the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`", is spelled out elementwise:
every global section integral over `k` lies in the image of `k`.  That is the form the proofs
consume and the form the sufficient conditions produce.

The base change is to `X̄ = X ×_k k̄`, built as the two-step pullback along the separable closure
`k_s` of `k` and then along `k̄`, so that Tag 038H can be used for the second step.  `X̄` has
finitely many irreducible components: over `k_s` this is the orbit decomposition of the fibres of
the component map (Tag 04KZ and its orbit form), and from `k_s` to `k̄` the components correspond
bijectively (Tag 038H).

Rather than a single connected component of `X̄` as in the source, the proof uses *all* the
irreducible components `Z_i` of `X̄` with their reduced induced structure.  Each is integral and
locally of finite type over `k̄`, so Tag 04L5 gives that `𝒪(Z_i)^*/k̄^*` is finitely generated;
and `X̄ ⟶ X` is surjective because both base change projections are, so the `Z_i` jointly detect
vanishing of global sections of the reduced scheme `X`.  A unit `u` of `Γ(X, 𝒪_X)` in the kernel
of `𝒪(X)^* → ∏ 𝒪(Z_i)^*/k̄^*` restricts to a constant `b_i ∈ k̄` on each `Z_i`; the product `P` of
the minimal polynomials of the `b_i` over `k` is monic and kills `u` on every `Z_i`, hence kills
`u`.  So `u` is integral over `k`, condition (1) makes it a constant, and `k` being a field makes
that constant a unit.  Hence that kernel is exactly `k^*`, and `𝒪(X)^*/k^*` embeds in a finite
product of finitely generated abelian groups.

The reduction of (2) to (1) is the source's: a `k`-rational point gives a ring retraction
`Γ(X, 𝒪_X) → k`, whose restriction to the integral closure of `k` is a map out of a field (Tag
04MI) and hence injective, which forces a section integral over `k` to equal the constant its
image names.

## References

* [Stacks Project, Tag 04L7](https://stacks.math.columbia.edu/tag/04L7)
* [Stacks Project, Tag 04L5](https://stacks.math.columbia.edu/tag/04L5)
* [Stacks Project, Tag 04KZ](https://stacks.math.columbia.edu/tag/04KZ)
* [Stacks Project, Tag 038H](https://stacks.math.columbia.edu/tag/038H)
* [Stacks Project, Tag 04MI](https://stacks.math.columbia.edu/tag/04MI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The reduced induced closed subscheme structure on an irreducible component. -/
private noncomputable def reducedComponent {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme

/-- The closed immersion of an irreducible component with its reduced induced structure. -/
private noncomputable def reducedComponentι {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) : reducedComponent C hC ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι

private instance isClosedImmersion_reducedComponentι {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) :
    IsClosedImmersion (reducedComponentι C hC) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal _).subschemeι)

private instance isReduced_reducedComponent {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) : IsReduced (reducedComponent C hC) :=
  inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme)

private theorem range_reducedComponentι {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) :
    Set.range (reducedComponentι C hC) = C :=
  Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _

private theorem isIntegral_reducedComponent {X : Scheme.{u}} (C : Set X)
    (hC : C ∈ irreducibleComponents (X : Type u)) : IsIntegral (reducedComponent C hC) :=
  have : IrreducibleSpace (reducedComponent C hC) :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
      rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; exact hC.1)
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Stacks Tag 04L5 for an irreducible component with its reduced induced structure.** -/
private theorem fg_units_quotient_reducedComponent (K : Type u) [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [LocallyOfFiniteType g] (C : Set Z)
    (hC : C ∈ irreducibleComponents (Z : Type u)) :
    Group.FG (Γ(reducedComponent C hC, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of K)).inv ≫
        (reducedComponentι C hC ≫ g).appTop).hom).toMonoidHom).range) := by
  have : IsIntegral (reducedComponent C hC) := isIntegral_reducedComponent C hC
  have : LocallyOfFiniteType (reducedComponentι C hC) :=
    IsImmersion.instLocallyOfFiniteType (reducedComponentι C hC)
  have : LocallyOfFiniteType (reducedComponentι C hC ≫ g) := locallyOfFiniteType_comp _ _
  exact fg_units_quotient_of_locallyOfFiniteType K (reducedComponentι C hC ≫ g)

/-- A global section of a reduced scheme which pulls back to zero along every member of a jointly
surjective family of morphisms is zero. -/
private theorem eq_zero_of_appTop_eq_zero_of_jointly_surjective {X : Scheme.{u}} [IsReduced X]
    {ι : Type*} {Y : ι → Scheme.{u}} (r : ∀ i, Y i ⟶ X)
    (hcover : ∀ x : X, ∃ i y, (r i) y = x) (s : Γ(X, ⊤))
    (hs : ∀ i, (r i).appTop.hom s = 0) : s = 0 := by
  refine (basicOpen_eq_bot_iff s).mp (le_antisymm ?_ bot_le)
  intro x hx
  obtain ⟨i, y, rfl⟩ := hcover x
  have hy : y ∈ (Y i).basicOpen ((r i).appTop s) := by
    rw [← Scheme.Hom.preimage_basicOpen_top]
    exact hx
  rw [hs i, Scheme.basicOpen_zero] at hy
  exact hy.elim

/-- The base change of a scheme locally of finite type over a field to an algebraic closure, taken
in two steps through the separable closure, has finitely many irreducible components if the scheme
does.

Over the separable closure the fibres of the map sending a component to its image are finite, by
the orbit decomposition of Tag 04KZ; from the separable closure to the algebraic closure the
components correspond bijectively, by Tag 038H. -/
@[ega "IV 4.4.1" "special case"]
private theorem finite_irreducibleComponents_baseChange_algebraicClosure
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hX : (irreducibleComponents (X : Type u)).Finite) :
    let Kₛ := SeparableClosure k
    let gₛ := Spec.map (CommRingCat.ofHom (algebraMap k Kₛ))
    let K := AlgebraicClosure k
    let gₛK := Spec.map (CommRingCat.ofHom (algebraMap Kₛ K))
    (irreducibleComponents
      (pullback (C := Scheme.{u}) (pullback.snd f gₛ) gₛK)).Finite := by
  classical
  let Kₛ := SeparableClosure k
  let gₛ := Spec.map (CommRingCat.ofHom (algebraMap k Kₛ))
  let Xₛ := pullback (C := Scheme.{u}) f gₛ
  let p := pullback.fst f gₛ
  let Xover : Over (Spec (.of k)) := Over.mk f
  let imageComponent : Set Xₛ → Set X := fun Z => p.base '' Z
  have : LocallyOfFiniteType Xover.hom := inferInstanceAs (LocallyOfFiniteType f)
  have hfiniteₛ : (irreducibleComponents Xₛ).Finite :=
    Set.Finite.of_finite_fibers imageComponent (s := irreducibleComponents Xₛ)
      (hX.subset (by
        rintro T ⟨Z, hZ, rfl⟩
        exact AlgebraicGeometry.mapsTo_irreducibleComponents_baseChange k Kₛ X f hZ))
      (by
        rintro T ⟨W, hW, rfl⟩
        let Tcomp : irreducibleComponents X :=
          ⟨p.base '' W, AlgebraicGeometry.mapsTo_irreducibleComponents_baseChange k Kₛ X f hW⟩
        obtain ⟨s, hsne, hdecomp, horbit⟩ :=
          AlgebraicGeometry.exists_finite_single_orbit_decomposition
            (k := k) (K := Kₛ) Xover Tcomp
        have hdecomp' : p.base ⁻¹' (Tcomp : Set X) = ⋃ V ∈ s, V.1 := by
          simpa [p, Xover] using hdecomp
        let sSet : Finset (Set Xₛ) := s.attach.image fun V => V.1.1
        have hsSet : ((sSet : Finset (Set Xₛ)) : Set (Set Xₛ)).Finite := sSet.finite_toSet
        apply hsSet.subset
        rintro Z ⟨hZcomp, hZT⟩
        have hZT' : p.base '' Z = p.base '' W := by
          simpa [imageComponent] using hZT
        have hZsUnion : Z ⊆ ⋃₀ (sSet : Set (Set Xₛ)) := by
          intro x hx
          have hxT : x ∈ p.base ⁻¹' (Tcomp : Set X) := by
            show p.base x ∈ p.base '' W
            rw [← hZT']
            exact ⟨x, hx, rfl⟩
          rw [hdecomp'] at hxT
          rcases Set.mem_iUnion.mp hxT with ⟨V, hxV⟩
          rcases Set.mem_iUnion.mp hxV with ⟨hV, hxV⟩
          exact Set.mem_sUnion_of_mem hxV <| Finset.mem_image.mpr
            ⟨⟨V, hV⟩, Finset.mem_attach _ _, rfl⟩
        have hsSetComp : (sSet : Set (Set Xₛ)) ⊆ irreducibleComponents Xₛ := by
          intro V hV
          rcases Finset.mem_image.mp hV with ⟨V', -, rfl⟩
          exact V'.1.2
        exact mem_of_subset_sUnion_irreducibleComponents
          Z hZcomp (sSet : Set (Set Xₛ)) hsSet hsSetComp hZsUnion)
  let K := AlgebraicClosure k
  let fₛ := pullback.snd f gₛ
  let gₛK := Spec.map (CommRingCat.ofHom (algebraMap Kₛ K))
  have hbij :=
    AlgebraicGeometry.bijOn_irreducibleComponents_baseChange_of_isSepClosed Kₛ K Xₛ fₛ
  exact hfiniteₛ.of_injOn hbij.mapsTo hbij.injOn

/-- **Stacks Project, Tag 04L7 under its condition (1).** Let `k` be a field and let `X` be a
connected reduced scheme, locally of finite type over `k`, with finitely many irreducible
components, and assume that every global section of `X` integral over `k` is a constant — that is,
that the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`.  Then the group of invertible global
functions on `X` modulo the constants coming from `k` is a finitely generated abelian group.

The base change `X̄ = X ×_k \bar k` is surjective over `X` and has finitely many irreducible
components; each of them with its reduced induced structure is integral and locally of finite type
over `\bar k`, so Tag 04L5 applies to it.  A unit of `Γ(X, 𝒪_X)` which is a constant from
`\bar k` on every component of `X̄` is killed by the product of the minimal polynomials of those
constants over `k`, hence is integral over `k`, hence is a constant from `k` by the hypothesis.

Connectedness of `X` is one of the source's hypotheses and is kept here, but this proof does not
use it: in the source connectedness is what forces the constants on the components to agree,
whereas here condition (1) does that work. -/
@[stacks 04L7 "integral_closure_of_ground_field_is_ground_field"]
theorem fg_units_quotient_of_integrallyClosed (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] [LocallyOfFiniteType f]
    (hX : (irreducibleComponents (X : Type u)).Finite)
    (h1 : ∀ a : Γ(X, ⊤), (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).IsIntegralElem a →
      a ∈ Set.range ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) := by
  classical
  let Kₛ := SeparableClosure k
  let gₛ := Spec.map (CommRingCat.ofHom (algebraMap k Kₛ))
  let fₛ := pullback.snd f gₛ
  let K := AlgebraicClosure k
  let gₛK := Spec.map (CommRingCat.ofHom (algebraMap Kₛ K))
  let Xbar := pullback (C := Scheme.{u}) fₛ gₛK
  let fbar := pullback.snd fₛ gₛK
  let q : Xbar ⟶ X := pullback.fst fₛ gₛK ≫ pullback.fst f gₛ
  have : LocallyOfFiniteType fₛ := inferInstance
  have : LocallyOfFiniteType fbar := inferInstance
  have hXbar : (irreducibleComponents Xbar).Finite :=
    finite_irreducibleComponents_baseChange_algebraicClosure k X f hX
  let ι := {C : Set Xbar // C ∈ irreducibleComponents Xbar}
  let _ : Fintype ι := hXbar.fintype
  let Y : ι → Scheme.{u} := fun i => reducedComponent i.val i.property
  let g : ∀ i : ι, Y i ⟶ Xbar := fun i => reducedComponentι i.val i.property
  let r : ∀ i : ι, Y i ⟶ X := fun i => g i ≫ q
  let ρ : ∀ i : ι, Γ(X, ⊤) →+* Γ(Y i, ⊤) := fun i => (r i).appTop.hom
  let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let φᵢ : ∀ i : ι, K →+* Γ(Y i, ⊤) := fun i =>
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (g i ≫ fbar).appTop).hom
  let Hᵢ : ∀ i : ι, Subgroup (Γ(Y i, ⊤)ˣ) := fun i => (Units.map (φᵢ i).toMonoidHom).range
  let Q : ι → Type u := fun i => Γ(Y i, ⊤)ˣ ⧸ Hᵢ i
  let F : Γ(X, ⊤)ˣ →* ∀ i : ι, Q i :=
    MonoidHom.pi fun i => (QuotientGroup.mk' (Hᵢ i)).comp (Units.map (ρ i).toMonoidHom)
  let H₀ : Subgroup (Γ(X, ⊤)ˣ) := (Units.map φ.toMonoidHom).range
  have hcomm (i : ι) : (ρ i).comp φ = (φᵢ i).comp (algebraMap k K) := by
    let α : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
    have hbase : (r i) ≫ f = (g i ≫ fbar) ≫ α := by
      dsimp only [r, q]
      calc
        _ = g i ≫ pullback.fst fₛ gₛK ≫ (pullback.fst f gₛ ≫ f) := by simp [Category.assoc]
        _ = g i ≫ pullback.fst fₛ gₛK ≫ (pullback.snd f gₛ ≫ gₛ) := by rw [pullback.condition]
        _ = g i ≫ (pullback.fst fₛ gₛK ≫ pullback.snd f gₛ) ≫ gₛ := by simp [Category.assoc]
        _ = g i ≫ (fbar ≫ gₛK) ≫ gₛ := by rw [pullback.condition]
        _ = (g i ≫ fbar) ≫ α := by
          simp only [Category.assoc]
          rw [← Spec.map_comp]
          rfl
    have htop := congrArg (fun h : Scheme.Hom _ _ => h.appTop.hom) hbase
    have htop' : (r i).appTop.hom.comp f.appTop.hom =
        (g i ≫ fbar).appTop.hom.comp α.appTop.hom := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using htop
    have hnatCat : CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv =
        (Scheme.ΓSpecIso (.of k)).inv ≫ α.appTop := by
      simp [α]
    have hnat : α.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom =
        (Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K) :=
      (congrArg CommRingCat.Hom.hom hnatCat).symm
    calc
      _ = ((r i).appTop.hom.comp f.appTop.hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom := rfl
      _ = ((g i ≫ fbar).appTop.hom.comp α.appTop.hom).comp
          (Scheme.ΓSpecIso (.of k)).inv.hom := by rw [htop']
      _ = (g i ≫ fbar).appTop.hom.comp
          ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) := by
        rw [RingHom.comp_assoc, hnat]
  have hfgᵢ (i : ι) : Group.FG (Q i) :=
    fg_units_quotient_reducedComponent K fbar i.val i.property
  have hfgPi : Group.FG (∀ i : ι, Q i) := by
    rw [Group.fg_def, ← Subgroup.pi_top]
    exact Subgroup.FG.pi fun i => (hfgᵢ i).out
  have hcover : ∀ x : X, ∃ i y, (r i) y = x := by
    intro x
    have hq : Function.Surjective q.base :=
      (surjective_iff q).mp inferInstance
    obtain ⟨z, hz⟩ := hq x
    have hzcover : z ∈ ⋃₀ irreducibleComponents Xbar := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ z
    obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp hzcover
    obtain ⟨y, hy⟩ : ∃ y : Y ⟨C, hC⟩, (g ⟨C, hC⟩) y = z :=
      Set.mem_range.mp ((range_reducedComponentι C hC).symm ▸ hzC)
    refine ⟨⟨C, hC⟩, y, ?_⟩
    show q ((g ⟨C, hC⟩) y) = x
    rw [hy]
    exact hz
  have hsub : H₀ ≤ F.ker := by
    intro u hu
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hu
    rw [MonoidHom.mem_ker, ← ha]
    funext i
    have hunit : Units.map (ρ i).toMonoidHom (Units.map φ.toMonoidHom a) =
        Units.map (φᵢ i).toMonoidHom (Units.map (algebraMap k K).toMonoidHom a) :=
      Units.ext (congrArg (fun h : k →+* Γ(Y i, ⊤) => h a.val) (hcomm i))
    show (QuotientGroup.mk' (Hᵢ i))
      (Units.map (ρ i).toMonoidHom (Units.map φ.toMonoidHom a)) = 1
    rw [hunit]
    exact (QuotientGroup.eq_one_iff _).2
      (MonoidHom.mem_range.mpr ⟨Units.map (algebraMap k K).toMonoidHom a, rfl⟩)
  have hker : F.ker ≤ H₀ := by
    intro u hu
    have hmem (i : ι) : Units.map (ρ i).toMonoidHom u ∈ Hᵢ i :=
      (QuotientGroup.eq_one_iff _).mp (congrFun hu i)
    choose b hb using fun i => MonoidHom.mem_range.mp (hmem i)
    have hbval (i : ι) : ρ i u.val = φᵢ i (b i).val := (congrArg Units.val (hb i)).symm
    let P : Polynomial k := ∏ i : ι, minpoly k (b i).val
    have hPmonic : P.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ =>
        minpoly.monic (Algebra.IsAlgebraic.isAlgebraic (b i).val).isIntegral
    have hPzeroK (i : ι) : Polynomial.eval₂ (algebraMap k K) (b i).val P = 0 := by
      have hprod : ∏ j : ι, Polynomial.eval₂ (algebraMap k K) (b i).val
          (minpoly k (b j).val) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [← Polynomial.aeval_def, minpoly.aeval]
      simpa [P, Polynomial.eval₂_finsetProd] using hprod
    have hz : Polynomial.eval₂ φ u.val P = 0 := by
      refine eq_zero_of_appTop_eq_zero_of_jointly_surjective r hcover _ fun i => ?_
      calc ρ i (Polynomial.eval₂ φ u.val P)
          = Polynomial.eval₂ ((ρ i).comp φ) (ρ i u.val) P :=
            Polynomial.hom_eval₂ P φ (ρ i) u.val
        _ = Polynomial.eval₂ ((φᵢ i).comp (algebraMap k K)) (φᵢ i (b i).val) P := by
            rw [hcomm i, hbval i]
        _ = φᵢ i (Polynomial.eval₂ (algebraMap k K) (b i).val P) :=
            (Polynomial.hom_eval₂ P (algebraMap k K) (φᵢ i) (b i).val).symm
        _ = 0 := by rw [hPzeroK i, map_zero]
    obtain ⟨a, ha⟩ := h1 u.val ⟨P, hPmonic, hz⟩
    by_cases ha0 : a = 0
    · have hv0 : u.val = 0 := by rw [← ha, ha0, map_zero]
      have : Subsingleton Γ(X, ⊤) :=
        subsingleton_of_zero_eq_one (isUnit_zero_iff.mp (hv0 ▸ u.isUnit))
      exact MonoidHom.mem_range.mpr ⟨1, Units.ext (Subsingleton.elim _ _)⟩
    · exact MonoidHom.mem_range.mpr ⟨Units.mk0 a ha0, Units.ext ha⟩
  exact Group.fg_quotient_of_ker_eq F (le_antisymm hker hsub)

/-- The ring-theoretic step from condition (2) of Stacks Tag 04L7 to condition (1).

If the structure map `k → A` of an algebra over a field admits a ring retraction `σ` and the
integral closure of `k` in `A` is a field, then every element of `A` integral over `k` is a
constant.

The retraction restricted to the integral closure is a ring map out of a field, hence injective,
and `a` and the constant named by `σ a` have the same image under it. -/
private theorem mem_range_algebraMap_of_isIntegral_of_retraction {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] (σ : A →+* k) (hσ : ∀ c : k, σ (algebraMap k A c) = c)
    (hfield : IsField (integralClosure k A)) {a : A} (ha : _root_.IsIntegral k a) :
    a ∈ Set.range (algebraMap k A) := by
  have hτinj : Function.Injective
      (σ.comp (Subalgebra.val (integralClosure k A)).toRingHom) := by
    intro x y hxy
    by_contra hne
    obtain ⟨z, hz⟩ := hfield.mul_inv_cancel (sub_ne_zero.mpr hne)
    have hzero : (σ.comp (Subalgebra.val (integralClosure k A)).toRingHom) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    refine one_ne_zero (α := k) ?_
    rw [← map_one (σ.comp (Subalgebra.val (integralClosure k A)).toRingHom), ← hz, map_mul,
      hzero, zero_mul]
  refine ⟨σ a, congrArg Subtype.val (hτinj (a₁ := ⟨algebraMap k A (σ a),
    Subalgebra.algebraMap_mem _ _⟩) (a₂ := ⟨a, ha⟩) ?_)⟩
  exact hσ (σ a)

/-- **Stacks Tag 04L7, condition (2) implies condition (1).** Let `X` be a connected reduced
scheme over a field `k` which has a `k`-rational point.  Then every global section of `X` which is
integral over `k` is a constant, i.e. the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`.

A `k`-rational point gives a retraction of `k → Γ(X, 𝒪_X)` on global sections.  By Tag 04MI the
integral closure of `k` in `Γ(X, 𝒪_X)` is a field, so the retraction is injective on it, and a
section integral over `k` is forced to equal the constant named by its image. -/
theorem mem_range_of_isIntegralElem_of_rationalPoint (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] (e : Spec (.of k) ⟶ X)
    (he : e ≫ f = 𝟙 (Spec (.of k))) (a : Γ(X, ⊤))
    (ha : (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).IsIntegralElem a) :
    a ∈ Set.range ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom := by
  let _ : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hmor : (Scheme.ΓSpecIso (.of k)).inv ≫ ((f.appTop ≫ e.appTop) ≫
      (Scheme.ΓSpecIso (.of k)).hom) = 𝟙 (CommRingCat.of k) := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  exact mem_range_algebraMap_of_isIntegral_of_retraction
    (e.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
    (fun c => congrArg (fun m : CommRingCat.of k ⟶ CommRingCat.of k => m.hom c) hmor)
    (integralClosure_globalSections_isField k X f) ha

/-- **Over an algebraically closed field condition (1) of Stacks Tag 04L7 is automatic.** Every
global section of a connected reduced scheme over an algebraically closed field `k` which is
integral over `k` is a constant.

By Tag 04MI the integral closure of `k` in the global sections is a field, hence a domain, and a
domain integral over an algebraically closed field is that field. -/
theorem mem_range_of_isIntegralElem_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] (a : Γ(X, ⊤))
    (ha : (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).IsIntegralElem a) :
    a ∈ Set.range ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom := by
  let _ : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : IsDomain (integralClosure k Γ(X, ⊤)) :=
    (integralClosure_globalSections_isField k X f).isDomain
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := k) (K := integralClosure k Γ(X, ⊤))).2 ⟨a, ha⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- **Stacks Project, Tag 04L7 under its condition (2).** Let `k` be a field and let `X` be a
connected reduced scheme, locally of finite type over `k`, with finitely many irreducible
components, and suppose `X` has a `k`-rational point.  Then the group of invertible global
functions on `X` modulo the constants coming from `k` is a finitely generated abelian group.

Condition (2) implies condition (1) by `mem_range_of_isIntegralElem_of_rationalPoint`, which is
the source's own argument. -/
@[stacks 04L7 "rational_point"]
theorem fg_units_quotient_of_rationalPoint (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] [LocallyOfFiniteType f]
    (hX : (irreducibleComponents (X : Type u)).Finite) (e : Spec (.of k) ⟶ X)
    (he : e ≫ f = 𝟙 (Spec (.of k))) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) :=
  fg_units_quotient_of_integrallyClosed k X f hX
    (mem_range_of_isIntegralElem_of_rationalPoint k X f e he)

end AlgebraicGeometry

end
