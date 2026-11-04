module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.RingTheory.RelativeDimension.ValuationRing
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Fibres of a morphism to the spectrum of a valuation ring

Let an irreducible scheme map surjectively and locally of finite type to the spectrum of a
valuation ring. Then its special fibre is equidimensional, and its dimension equals the
dimension of the generic fibre.

## Main results

* `AlgebraicGeometry.specialFiber_equidimensional`: the special fibre is equidimensional.
* `AlgebraicGeometry.topologicalKrullDim_specialFiber_eq_genericFiber`: the special and generic
  fibres have the same dimension.

## Implementation notes

The fibres are Mathlib's scheme-theoretic fibres `AlgebraicGeometry.Scheme.Hom.fiber`. The
closed point of the spectrum of the valuation ring is its maximal ideal and its generic point
is the zero ideal, so both fibres are named by explicit prime ideals rather than through
`genericPoint`. Dimension is the Krull dimension of the underlying topological space.

Both statements reduce to one pointwise computation: the local dimension of the special fibre
at *any* of its points equals the dimension of the generic fibre. That computation is made on
an affine chart, where it becomes the corresponding statement for the two fibre rings of a
finite-type algebra over a valuation ring. Passing to the reduced induced subscheme on the
whole space (which is a homeomorphism) supplies the reducedness the chart computation needs.

## References

* [Stacks Project, Tag 0B2J](https://stacks.math.columbia.edu/tag/0B2J)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The residue field of a local ring, as an object of `CommRingCat` built from the quotient
ring structure, is isomorphic to the one built from its field structure. -/
private noncomputable def residueFieldCommRingIso (A : Type u) [CommRing A] [IsLocalRing A] :
    @CommRingCat.of (IsLocalRing.ResidueField A) (IsLocalRing.instCommRingResidueField A) ≅
      @CommRingCat.of (IsLocalRing.ResidueField A)
        (Field.toCommRing (K := IsLocalRing.ResidueField A)) := by
  let κ := IsLocalRing.ResidueField A
  let c₁ : CommRing κ := IsLocalRing.instCommRingResidueField A
  let c₂ : CommRing κ := Field.toCommRing (K := κ)
  let : CommRing κ := c₁
  let n₁ : NonAssocSemiring κ := inferInstance
  let : CommRing κ := c₂
  let n₂ : NonAssocSemiring κ := inferInstance
  let f : @RingHom κ κ n₁ n₂ :=
    { toFun := id, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let g : @RingHom κ κ n₂ n₁ :=
    { toFun := id, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact {
    hom := @CommRingCat.ofHom κ κ c₁ c₂ f
    inv := @CommRingCat.ofHom κ κ c₂ c₁ g
    hom_inv_id := by apply CommRingCat.hom_ext; ext x; rfl
    inv_hom_id := by apply CommRingCat.hom_ext; ext x; rfl }

/-- A continuous surjection between sober irreducible spaces takes the generic point to the
generic point. -/
private theorem surjective_maps_genericPoint {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space X] [QuasiSober X] [IrreducibleSpace X] [T0Space Y]
    [QuasiSober Y] [IrreducibleSpace Y] (f : X → Y) (hf : Function.Surjective f)
    (hcont : Continuous f) :
    f (genericPoint X) = genericPoint Y := by
  have himage : f '' (Set.univ : Set X) = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ.mpr hf]
  have hgen : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa [himage] using (genericPoint_spec X).image hcont
  exact (genericPoint_spec Y).eq hgen |>.symm

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
private theorem genericPoint_mem_of_mem {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  (genericPoint_spec X).mem_open_set_iff U.isOpen |>.2 (by simpa using ⟨x, hx⟩)

/-- Two morphisms into the same target that agree along a homeomorphism of their sources have
homeomorphic fibres over every point. -/
private noncomputable def fiberHomeomorphOfHomeomorph
    {X Y Z : Scheme.{u}} (e : X ≃ₜ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (h : ∀ x, f (e x) = g x) (z : Z) : g.fiber z ≃ₜ f.fiber z :=
  (g.fiberHomeo z).trans <|
    (e.subtype (p := fun x ↦ g x = z) (q := fun y ↦ f y = z)
      (fun x ↦ by rw [h x])).trans (f.fiberHomeo z).symm

/-- Postcomposing with an injective morphism does not change the fibres. -/
private noncomputable def fiberHomeomorph_comp_injective {X V S : Scheme.{u}}
    (g : X ⟶ V) (k : V ⟶ S) (hk : Function.Injective k) (x : X) :
    (g ≫ k).fiber ((g ≫ k) x) ≃ₜ g.fiber (g x) := by
  let A : Set X := (g ≫ k) ⁻¹' {(g ≫ k) x}
  let B : Set X := g ⁻¹' {g x}
  have hAB : A = B := by
    ext y
    simpa only [A, B, Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
      using hk.eq_iff
  exact ((g ≫ k).fiberHomeo _).trans <| (Homeomorph.setCongr hAB).trans (g.fiberHomeo _).symm

/-- The relative dimension at a prime of the source is the local Krull dimension of the fibre
ring at the corresponding point. -/
private theorem relativeDimensionAt_eq_localKrullDim_preimage {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)
    (z : ↥(PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p})) :
    Algebra.relativeDimensionAt A (z : PrimeSpectrum B).asIdeal =
      TopologicalSpace.localKrullDim (PrimeSpectrum (p.asIdeal.Fiber B))
        (PrimeSpectrum.preimageHomeomorphFiber A B p z) := by
  obtain ⟨q, hq⟩ := z
  subst hq
  rw [Algebra.relativeDimensionAt, topologicalKrullDimAt_eq_of_homeomorph
    (PrimeSpectrum.preimageHomeomorphFiber A B (PrimeSpectrum.comap (algebraMap A B) q)),
    topologicalKrullDimAt_eq_localKrullDim]

/-- For a finite-type algebra over a valuation ring, the fibre ring over the maximal ideal is
equidimensional of the dimension of the fibre ring over the zero ideal. -/
private theorem localKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot
    {R S : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (x : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) :
    localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) x =
      ringKrullDim ((⊥ : Ideal R).Fiber S) := by
  have hfib : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨x⟩
  have hdim :=
    ValuationRing.ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional
      hfib
  let T := (IsLocalRing.maximalIdeal R).Fiber S
  have : Algebra.FiniteType (IsLocalRing.maximalIdeal R).ResidueField T := inferInstance
  have hcomp : ∀ y : PrimeSpectrum T,
      localKrullDim (PrimeSpectrum T) y = topologicalKrullDim (irreducibleComponent y) := by
    intro y
    rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
      (IsLocalRing.maximalIdeal R).ResidueField y).1]
    refine le_antisymm (iSup₂_le fun Z hZ => le_of_eq (hdim.2 Z hZ.1 _
      (irreducibleComponent_mem_irreducibleComponents y)))
      (le_iSup₂_of_le (irreducibleComponent y)
        ⟨irreducibleComponent_mem_irreducibleComponents y, mem_irreducibleComponent⟩ le_rfl)
  have hglobal : localKrullDim (PrimeSpectrum T) x = ringKrullDim T := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      topologicalKrullDim_eq_iSup_localKrullDim]
    refine le_antisymm (le_iSup _ x) (iSup_le fun y => ?_)
    rw [hcomp y, hcomp x]
    exact le_of_eq (hdim.2 _ (irreducibleComponent_mem_irreducibleComponents y) _
      (irreducibleComponent_mem_irreducibleComponents x))
  exact hglobal.trans hdim.1

/-- The dimension of a fibre of a morphism of affine schemes is the dimension of the fibre
ring. -/
private theorem topologicalKrullDim_specMap_fiber_eq_ringKrullDim {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p) =
      ringKrullDim (p.asIdeal.Fiber B) := by
  let e := Spec.fiberToSpecResidueFieldIso A B p
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ e.hom.left.homeomorph.isHomeomorph

/-- The generic fibre of a surjective morphism between irreducible schemes is irreducible. -/
private theorem genericFiber_irreducible {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [Surjective f] :
    IrreducibleSpace (f.fiber (genericPoint Y)) := by
  let η := genericPoint Y
  let F : Set X := f ⁻¹' {η}
  have hη : f (genericPoint X) = η :=
    surjective_maps_genericPoint f f.surjective f.continuous
  let g : F := ⟨genericPoint X, by simp [F, hη]⟩
  have hg : IsGenericPoint g (Set.univ : Set F) := by
    rw [isGenericPoint_def]
    ext z
    rw [closure_subtype]
    simp only [Set.image_singleton]
    change (z : X) ∈ closure ({genericPoint X} : Set X) ↔ z ∈ Set.univ
    rw [(genericPoint_spec X).def]
    simp
  have : PreirreducibleSpace F := ⟨hg.isIrreducible.2⟩
  have : IrreducibleSpace F := ⟨⟨g⟩⟩
  exact (f.fiberHomeo η).symm.surjective.irreducibleSpace (f.fiberHomeo η).symm.continuous

/-- The generic point of the spectrum of a domain corresponds to the zero ideal of its ring of
global functions. -/
private theorem primeIdealOf_genericPoint_eq_bot {R : Type u} [CommRing R] [IsDomain R] :
    let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    U.2.primeIdealOf ⟨genericPoint (Spec (.of R)), Set.mem_univ _⟩ =
      (⊥ : Ideal Γ(Spec (.of R), ⊤)) := by
  classical
  dsimp only
  let A := Γ(Spec (.of R), ⊤)
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let h := U.2.fromSpec
  have : IsOpenImmersion h := U.2.isOpenImmersion_fromSpec
  have hsurj : Function.Surjective h := fun x => by
    rw [← Set.mem_range, U.2.range_fromSpec]
    exact Set.mem_univ x
  have hg := surjective_maps_genericPoint h hsurj h.continuous
  have hq : U.2.primeIdealOf ⟨genericPoint (Spec (.of R)), Set.mem_univ _⟩ =
      genericPoint (PrimeSpectrum A) :=
    h.isOpenEmbedding.injective ((U.2.fromSpec_primeIdealOf _).trans hg.symm)
  rw [hq]
  exact congrArg PrimeSpectrum.asIdeal (genericPoint_eq_bot_of_affine A)

/-- A closed point of the spectrum of a ring corresponds to a maximal ideal of its ring of
global functions. -/
private theorem primeIdealOf_closedPoint_isMaximal {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (hp : p.asIdeal.IsMaximal) :
    let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    (U.2.primeIdealOf ⟨p, Set.mem_univ _⟩).asIdeal.IsMaximal := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  exact U.2.primeIdealOf_isMaximal_of_isClosed _
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hp)

/-- On a suitable affine chart around a point of the special fibre, the local dimension of that
fibre is the dimension of the chart's generic fibre ring. -/
private theorem specialFiber_localDimension_eq_affine_genericRingDim
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} [IrreducibleSpace X] [IsReduced X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [Surjective f]
    (x : X) (hx : f x = ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) :
    ∃ (V : X.affineOpens), x ∈ V.1 ∧
      (letI : Algebra (Γ(Spec (.of R), ⊤)) (Γ(X, V.1)) :=
        (f.appLE ⊤ V.1 (by simp)).hom.toAlgebra
       topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
        ringKrullDim ((⊥ : Ideal Γ(Spec (.of R), ⊤)).Fiber Γ(X, V.1))) := by
  obtain ⟨_, ⟨Vopen, hVopen, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : X.affineOpens := ⟨Vopen, hVopen⟩
  have : Nonempty (V.1 : Set X) := ⟨⟨x, hxV⟩⟩
  have : IrreducibleSpace V.1 := V.1.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have : IsReduced (Spec (.of Γ(X, V.1))) := isReduced_of_isOpenImmersion V.2.fromSpec
  have : IrreducibleSpace (Spec (.of Γ(X, V.1))) :=
    V.2.isoSpec.hom.homeomorph.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral (Spec (.of Γ(X, V.1))) := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsDomain Γ(X, V.1) := (affine_isIntegral_iff (.of Γ(X, V.1))).mp inferInstance
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hVU : V.1 ≤ f ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by simp
  let g := f.appLE (⊤ : (Spec (.of R)).Opens) V.1 hVU
  let A := Γ(Spec (.of R), ⊤)
  let S := Γ(X, V.1)
  let : Algebra A S := g.hom.toAlgebra
  have : Algebra.FiniteType A S := f.finiteType_appLE (isAffineOpen_top _) V.2 hVU
  let e : A ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have : IsDomain A := e.toMulEquiv.isDomain R
  have : ValuationRing A := e.symm.surjective.valuationRing e.symm.toRingHom
  have : IsLocalRing A := (ValuationRing.iff_local_bezout_domain.mp inferInstance).1
  have hg : f (genericPoint X) = genericPoint (Spec (.of R)) :=
    surjective_maps_genericPoint f f.surjective f.continuous
  have hηV : genericPoint X ∈ V.1 := genericPoint_mem_of_mem V.1 hxV
  let qη : PrimeSpectrum S := V.2.primeIdealOf ⟨genericPoint X, hηV⟩
  have hqη : qη.asIdeal.comap (algebraMap A S) = ⊥ := by
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (⊤ : (Spec (.of R)).Opens)
      (isAffineOpen_top _) V.1 V.2 hVU hηV
    rw [hg] at hcomap
    exact congrArg PrimeSpectrum.asIdeal hcomap |>.trans (by
      simpa [A, U] using (primeIdealOf_genericPoint_eq_bot (R := R)))
  have hinj : Function.Injective (algebraMap A S) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ qη.asIdeal.comap (algebraMap A S) := by
      change algebraMap A S a ∈ qη.asIdeal
      rw [ha]
      exact qη.asIdeal.zero_mem
    rwa [hqη] at hmem
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  have hq : (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.comap (algebraMap A S) =
      IsLocalRing.maximalIdeal A := by
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (⊤ : (Spec (.of R)).Opens)
      (isAffineOpen_top _) V.1 V.2 hVU hxV
    let Utop : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    have hmax : (Utop.2.primeIdealOf ⟨f x, Set.mem_univ _⟩).asIdeal.IsMaximal := by
      simpa [hx, Utop] using
        (primeIdealOf_closedPoint_isMaximal
          (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)
          (show (IsLocalRing.maximalIdeal R).IsMaximal from inferInstance))
    have hmaxA : (Utop.2.primeIdealOf ⟨f x, Set.mem_univ _⟩).asIdeal =
        IsLocalRing.maximalIdeal A := by
      simpa [Utop, A] using IsLocalRing.eq_maximalIdeal hmax
    exact (congrArg PrimeSpectrum.asIdeal hcomap).trans hmaxA
  let p : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A, inferInstance⟩
  have hcomap : PrimeSpectrum.comap (algebraMap A S) (V.2.primeIdealOf ⟨x, hxV⟩) = p :=
    PrimeSpectrum.ext hq
  let z : ↥(PrimeSpectrum.comap (algebraMap A S) ⁻¹' {p}) :=
    ⟨V.2.primeIdealOf ⟨x, hxV⟩, hcomap⟩
  let x' := PrimeSpectrum.preimageHomeomorphFiber A S p z
  refine ⟨V, hxV, ?_⟩
  calc
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
        Algebra.relativeDimensionAt A (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
      simpa [A, U] using
        fiberDimensionAt_eq_relativeDimensionAt_chart f U V (by simp [U]) x hxV
    _ = localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal A).Fiber S)) x' :=
      relativeDimensionAt_eq_localKrullDim_preimage (A := Γ(Spec (.of R), ⊤)) (B := Γ(X, V.1)) p z
    _ = ringKrullDim ((⊥ : Ideal Γ(Spec (.of R), ⊤)).Fiber Γ(X, V.1)) := by
      simpa [A, S] using localKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot x'

/-- The reduced case of the pointwise statement: for a reduced irreducible source, the local
dimension of the special fibre at any point is the dimension of the generic fibre. -/
private theorem specialFiber_localDimension_eq_genericFiber_dimension_reduced
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} [IrreducibleSpace X] [IsReduced X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [Surjective f]
    (x : X) (hx : f x = ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDim (f.fiber (genericPoint (Spec (.of R)))) := by
  obtain ⟨V, hxV, hlocal⟩ := specialFiber_localDimension_eq_affine_genericRingDim f x hx
  let y := genericPoint (Spec (.of R))
  let j := V.2.fromSpec
  have : IsOpenImmersion j := V.2.isOpenImmersion_fromSpec
  let g := j ≫ f
  let m : g.fiber y ⟶ f.fiber y := Limits.pullback.map g
    ((Spec (.of R)).fromSpecResidueField y) f
    ((Spec (.of R)).fromSpecResidueField y) j (𝟙 _) (𝟙 _) (by simp [g]) (by simp)
  have : IsOpenImmersion m :=
    Scheme.pullback_map_isOpenImmersion g
      ((Spec (.of R)).fromSpecResidueField y) f
      ((Spec (.of R)).fromSpecResidueField y) j (𝟙 _) (𝟙 _) (by simp [g]) (by simp)
  have hg : f (genericPoint X) = y :=
    surjective_maps_genericPoint f f.surjective f.continuous
  have hηV : genericPoint X ∈ V.1 := genericPoint_mem_of_mem V.1 hxV
  let qη : PrimeSpectrum Γ(X, V.1) := V.2.primeIdealOf ⟨genericPoint X, hηV⟩
  have hjqη : j qη = genericPoint X := V.2.fromSpec_primeIdealOf ⟨genericPoint X, hηV⟩
  have hqy : g qη = y := by
    change f (j qη) = y
    rw [hjqη, hg]
  have hUopen : IsOpen (Set.range m) := m.isOpenEmbedding.isOpen_range
  have hUne : (Set.range m).Nonempty := ⟨_, hqy ▸ g.asFiber qη, rfl⟩
  let : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (Limits.pullback.snd f _)
    infer_instance
  have : IrreducibleSpace (f.fiber y) := genericFiber_irreducible f
  have hglobal := topologicalKrullDim_eq_of_isOpen
    ((Spec (.of R)).residueField y) (f.fiber y) (f.fiberToSpecResidueField y)
    (Set.range m) hUopen hUne
  let e : (Set.univ : Set (g.fiber y)) ≃ₜ Set.range m :=
    (m.isOpenEmbedding.isEmbedding.homeomorphImage (Set.univ : Set (g.fiber y))).trans
      (Homeomorph.setCongr (by rw [Set.image_univ]))
  have hchartOpen : topologicalKrullDim (g.fiber y) = topologicalKrullDim (Set.range m) := by
    calc
      topologicalKrullDim (g.fiber y) = topologicalKrullDim (Set.univ : Set (g.fiber y)) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm
      _ = topologicalKrullDim (Set.range m) :=
        IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hVU : V.1 ≤ f ⁻¹ᵁ U.1 := by simp [U]
  let : Algebra Γ(Spec (.of R), ⊤) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let α := Spec.map (f.appLE U.1 V.1 hVU)
  have hcomp : α ≫ U.2.fromSpec = g := IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 hVU
  let p : PrimeSpectrum Γ(Spec (.of R), U.1) := U.2.primeIdealOf ⟨y, Set.mem_univ _⟩
  have hp : U.2.fromSpec p = y := U.2.fromSpec_primeIdealOf ⟨y, Set.mem_univ _⟩
  have hp0 : p.asIdeal = ⊥ := by
    dsimp [p, U, y]
    exact primeIdealOf_genericPoint_eq_bot (R := R)
  have hαq : α qη = p := by
    apply U.2.fromSpec.isOpenEmbedding.injective
    change (α ≫ U.2.fromSpec) qη = U.2.fromSpec p
    rw [hcomp, hqy, hp]
  have hcompq : (α ≫ U.2.fromSpec) qη = y := by rw [hcomp, hqy]
  have hdimComp : topologicalKrullDim ((α ≫ U.2.fromSpec).fiber y) =
      topologicalKrullDim (α.fiber p) := by
    calc
      _ = topologicalKrullDim ((α ≫ U.2.fromSpec).fiber
          ((α ≫ U.2.fromSpec) qη)) := by rw [hcompq]
      _ = topologicalKrullDim (α.fiber (α qη)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (fiberHomeomorph_comp_injective α U.2.fromSpec
            U.2.fromSpec.isOpenEmbedding.injective qη).isHomeomorph
      _ = topologicalKrullDim (α.fiber p) := by rw [hαq]
  have hdimChart : topologicalKrullDim (g.fiber y) =
      ringKrullDim ((⊥ : Ideal Γ(Spec (.of R), ⊤)).Fiber Γ(X, V.1)) := by
    calc
      topologicalKrullDim (g.fiber y) =
          topologicalKrullDim ((α ≫ U.2.fromSpec).fiber y) := by rw [← hcomp]
      _ = topologicalKrullDim (α.fiber p) := hdimComp
      _ = ringKrullDim ((⊥ : Ideal Γ(Spec (.of R), ⊤)).Fiber Γ(X, V.1)) := by
        have hspec := topologicalKrullDim_specMap_fiber_eq_ringKrullDim
          (A := Γ(Spec (.of R), U.1)) (B := Γ(X, V.1)) p
        have hα : α = Spec.map (CommRingCat.ofHom
            (algebraMap Γ(Spec (.of R), U.1) Γ(X, V.1))) := rfl
        have hpb : p = (⟨⊥, inferInstance⟩ : PrimeSpectrum Γ(Spec (.of R), U.1)) :=
          PrimeSpectrum.ext hp0
        rw [hα, hspec, hpb]
  exact hlocal.trans (hdimChart.symm.trans (hchartOpen.trans hglobal.symm))

/-- The local dimension of the special fibre at any of its points is the dimension of the
generic fibre. -/
private theorem specialFiber_localDimension_eq_genericFiber_dimension
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [Surjective f]
    (z : f.fiber (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)) :
    topologicalKrullDimAt
        (f.fiber (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)) z =
      topologicalKrullDim (f.fiber (genericPoint (Spec (.of R)))) := by
  let I := X.nilradical
  let e := X.homeomorphNilradicalSubscheme
  let i := I.subschemeι
  let g := i ≫ f
  have : IsReduced I.subscheme := by
    simpa [I, Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (⊤ : Closeds X)
  have : IrreducibleSpace I.subscheme := by
    have he : I.subscheme ≃ₜ X := e
    exact he.symm.surjective.irreducibleSpace he.symm.continuous
  have heval : ∀ x : I.subscheme, e x = i x := fun _ => rfl
  have hsurjI : Function.Surjective i := fun x =>
    (e.surjective x).imp fun y hy => (heval y).symm.trans hy
  have : Surjective g := ⟨f.surjective.comp hsurjI⟩
  have : LocallyOfFiniteType g := by
    dsimp [g, i]
    infer_instance
  have hcomm : ∀ x : I.subscheme, f (e x) = g x := fun _ => rfl
  let s : Spec (.of R) := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let Es := fiberHomeomorphOfHomeomorph e f g hcomm s
  let z' : g.fiber s := Es.symm z
  have hloc : topologicalKrullDimAt (f.fiber s) z = topologicalKrullDimAt (g.fiber s) z' := by
    calc
      topologicalKrullDimAt (f.fiber s) z = topologicalKrullDimAt (f.fiber s) (Es z') := by
        rw [Es.apply_symm_apply]
      _ = topologicalKrullDimAt (g.fiber s) z' :=
        (topologicalKrullDimAt_eq_of_homeomorph Es z').symm
  let x' := g.fiberι s z'
  let s' := g x'
  have hs' : s' = s := (g.range_fiberι s).le ⟨z', rfl⟩
  let eFib : (g ⁻¹' ({s'} : Set (Spec (.of R)))) ≃ₜ (g ⁻¹' ({s} : Set (Spec (.of R)))) :=
    (Homeomorph.refl I.subscheme).subtype (p := fun x ↦ g x = s')
      (q := fun x ↦ g x = s) (fun _ ↦ by simp [hs'])
  let E' := (g.fiberHomeo s').trans (eFib.trans (g.fiberHomeo s).symm)
  let t' : g.fiber s' := g.asFiber x'
  have hpoint : E' t' = z' := by
    apply (g.fiberHomeo s).injective
    simp only [E', Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change g.fiberι (g x') (g.asFiber x') = g.fiberι s z'
    rw [g.fiberι_asFiber]
  have hred' : topologicalKrullDimAt (g.fiber s) z' =
      topologicalKrullDim (g.fiber (genericPoint (Spec (.of R)))) := by
    calc
      topologicalKrullDimAt (g.fiber s) z' =
          topologicalKrullDimAt (g.fiber s) (E' t') := by rw [hpoint]
      _ = topologicalKrullDimAt (g.fiber s') t' :=
        (topologicalKrullDimAt_eq_of_homeomorph E' t').symm
      _ = topologicalKrullDim (g.fiber (genericPoint (Spec (.of R)))) :=
        specialFiber_localDimension_eq_genericFiber_dimension_reduced g x' hs'
  let Eg := fiberHomeomorphOfHomeomorph e f g hcomm (genericPoint (Spec (.of R)))
  exact hloc.trans (hred'.trans (IsHomeomorph.topologicalKrullDim_eq _ Eg.isHomeomorph))

/-- A locally algebraic scheme over a field whose local dimension is the same at every point
is equidimensional. -/
private theorem equidimensional_of_constant_local_dimension
    (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {d : WithBot ℕ∞} (hd : ∀ y : Y, topologicalKrullDimAt Y y = d) :
    TopologicalSpace.Equidimensional Y := by
  intro Z hZ W hW
  have hcomponent : ∀ V ∈ irreducibleComponents Y, topologicalKrullDim V = d := by
    intro V hV
    let η : Y := hV.1.genericPoint
    have hηV : IsGenericPoint η V :=
      hV.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents V hV)
    have honly : ∀ U ∈ irreducibleComponents Y, η ∈ U → U = V := by
      intro U hU hηU
      have hVU : V ⊆ U := by
        rw [← hηV]
        exact closure_minimal (Set.singleton_subset_iff.mpr hηU)
          (isClosed_of_mem_irreducibleComponents U hU)
      exact (hV.2 hU.1 hVU).antisymm hVU
    have hlocal : topologicalKrullDimAt Y η = topologicalKrullDim V := by
      rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y q η]
      refine le_antisymm (iSup₂_le fun U hU => ?_) (le_iSup₂_of_le V ⟨hV, hηV.mem⟩ le_rfl)
      rw [honly U hU.1 hU.2]
    exact hlocal.symm.trans (hd η)
  exact (hcomponent Z hZ).trans (hcomponent W hW).symm

/-- **Stacks Project, Tag 0B2J (equidimensionality).** The special fibre of a surjective,
locally finite type morphism from an irreducible scheme to the spectrum of a valuation ring is
equidimensional. -/
@[stacks 0B2J "equidimensionality"]
lemma specialFiber_equidimensional {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IrreducibleSpace X]
    [LocallyOfFiniteType f] [Surjective f] :
    TopologicalSpace.Equidimensional
      (f.fiber (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)) := by
  let s : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let S : Scheme := Spec (.of R)
  let k := IsLocalRing.ResidueField (Localization.AtPrime s.asIdeal)
  let fieldInst := IsLocalRing.ResidueField.field (Localization.AtPrime s.asIdeal)
  have : Field k := fieldInst
  let q : f.fiber s ⟶ Spec (@CommRingCat.of k fieldInst.toCommRing) :=
    f.fiberToSpecResidueField s ≫
      Spec.map (Scheme.Spec.residueFieldIso (.of R) s).inv ≫
        Spec.map (residueFieldCommRingIso (Localization.AtPrime s.asIdeal)).inv
  let : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  let : LocallyOfFiniteType q := by infer_instance
  exact @equidimensional_of_constant_local_dimension k fieldInst (f.fiber s) q
    (inferInstance : LocallyOfFiniteType q)
    (topologicalKrullDim (f.fiber (genericPoint (Spec (.of R)))))
    (fun z => specialFiber_localDimension_eq_genericFiber_dimension f z)

/-- **Stacks Project, Tag 0B2J (dimension).** The special and generic fibres of a surjective,
locally finite type morphism from an irreducible scheme to the spectrum of a valuation ring
have the same dimension. -/
@[stacks 0B2J "equality of fibre dimensions",
  ega "IV 14.3.10" "surjective f",
  sga "3 XXV 4.3" "special case"]
lemma topologicalKrullDim_specialFiber_eq_genericFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IrreducibleSpace X]
    [LocallyOfFiniteType f] [Surjective f] :
    topologicalKrullDim
        (f.fiber (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)) =
      topologicalKrullDim (f.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  let s : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let Y := f.fiber s
  have : Nonempty Y := by
    obtain ⟨x, hx⟩ := f.surjective s
    exact ⟨(f.fiberHomeo s).symm ⟨x, hx⟩⟩
  have hgeneric : genericPoint (Spec (.of R)) = (⊥ : PrimeSpectrum R) := by
    simpa using (genericPoint_eq_bot_of_affine (CommRingCat.of R))
  have hbot : (⟨⊥, inferInstance⟩ : PrimeSpectrum R) = (⊥ : PrimeSpectrum R) :=
    PrimeSpectrum.ext rfl
  calc
    topologicalKrullDim Y = ⨆ z : Y, topologicalKrullDimAt Y z := by
      rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
      simp only [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    _ = ⨆ _z : Y, topologicalKrullDim (f.fiber (genericPoint (Spec (.of R)))) :=
      iSup_congr fun z => specialFiber_localDimension_eq_genericFiber_dimension f z
    _ = topologicalKrullDim (f.fiber (genericPoint (Spec (.of R)))) := iSup_const
    _ = topologicalKrullDim (f.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
      rw [hgeneric, hbot]

end AlgebraicGeometry
