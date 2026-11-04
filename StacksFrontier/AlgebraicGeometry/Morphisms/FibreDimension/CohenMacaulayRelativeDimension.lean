module

public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus

/-!
# Cohen-Macaulay fibres and pure relative dimension

A flat morphism of schemes locally of finite presentation whose fibres are Cohen-Macaulay
decomposes its source into open and closed pieces of pure relative dimension. The relative
dimension is a locally constant function on the source, whose value at `x` is the local Krull
dimension of the fibre through `x` at the corresponding point, and the pieces of the
decomposition are its level sets.

## Main definitions

* `AlgebraicGeometry.relativeDimensionFunction`: the locally constant relative dimension on the
  source.
* `AlgebraicGeometry.relativeDimensionOpen`: its level set of a given dimension.

## Main results

* `AlgebraicGeometry.exists_clopen_relativeDimension`: the clopen pieces, indexed by their
  relative dimensions.
* `AlgebraicGeometry.relativeDimensionFunction_apply`: the function is pointwise the local
  dimension of the corresponding fibre.
* `AlgebraicGeometry.relativeDimensionOpen_isClopen`,
  `AlgebraicGeometry.iSup_relativeDimensionOpen`,
  `AlgebraicGeometry.pairwise_disjoint_relativeDimensionOpen` and
  `AlgebraicGeometry.relativeDimensionOpen_relativeDimension`: the canonical decomposition.

## Implementation notes

Each piece of the decomposition is represented by an open `U d` whose underlying set is also
closed. The equality of their supremum with the whole source together with their pairwise
disjointness expresses the coproduct decomposition, and the restricted morphism is the composite
of the canonical open immersion with `f`.

The dimension function is a canonical construction on points, so the decomposition does not
depend on a choice of clopen pieces; its value is characterized by the local Krull dimension of
the fibre.

The bulk of the file is the private `AlgebraicGeometry.CohenMacaulayFiber` section, which
transports Cohen-Macaulayness of the local ring of a fibre between the four presentations the
argument moves through: the scheme-theoretic fibre of `f` at a point, the fibre of a restriction
of `f` to affine opens, the fibre of a base change along an isomorphism of arrows, and the
ring-theoretic fibre `T_q / p T_q` to which the openness theorem
`Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq` applies. These
transports are stated with the locally Noetherian hypothesis on the fibres as an explicit
argument, since that is the form in which Cohen-Macaulayness of a morphism is defined.

Cohen-Macaulayness of a morphism and its characterization by flatness with Cohen-Macaulay
fibres belong to a different part of the chapter decomposition; they are used here through
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` and
`AlgebraicGeometry.isCohenMacaulay_iff_flat_and_fibers`.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

public section

open CategoryTheory TopologicalSpace Function

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayFiber

/-- On an affine chart, the local ring of the scheme-theoretic fibre at the point induced by `q`
is Cohen–Macaulay exactly when the corresponding relative fibre ring is Cohen–Macaulay. -/
private theorem fiberLocalRing_isMaximalCohenMacaulay_iff
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (hf : ∀ y : Spec (.of R), IsLocallyNoetherian
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber y)) (q : PrimeSpectrum T) :
    let f : Spec (.of T) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R T))
    IsCohenMacaulayLocalRing ((f.fiber (f q)).presheaf.stalk (f.asFiber q)) ↔
      Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T)))))
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T))))) := by
  exact (affineFiber_cm_iff hf q).trans
    (affineFiberPoint_cm_iff_ring_locus hf q)

end CohenMacaulayFiber

theorem fiber_local_dimension_eq_of_equidimensional
    (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {d : ℕ}
    (he : TopologicalSpace.Equidimensional Y)
    (hd : topologicalKrullDim Y = (d : WithBot ℕ∞)) (y : Y) :
    topologicalKrullDimAt Y y = (d : WithBot ℕ∞) := by
  obtain ⟨Z, hZ, _, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      k Y q y
  have hconstant (x : Y) : topologicalKrullDimAt Y x = topologicalKrullDim Z := by
    obtain ⟨W, hW, _, hWdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
        k Y q x
    exact hWdim.symm.trans (he W hW Z hZ)
  have hglobal : topologicalKrullDim Y = topologicalKrullDim Z := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hconstant]
    exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le y le_rfl)
  exact (hconstant y).trans (hglobal.symm.trans hd)

public theorem equidimensional_of_constant_fiber_local_dimension
    (k : Type u) [Field k] (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {d : ℕ}
    (hd : ∀ y : Y, topologicalKrullDimAt Y y = (d : WithBot ℕ∞)) :
    TopologicalSpace.Equidimensional Y := by
  intro Z hZ W hW
  have hcomponent (V : Set Y) (hV : V ∈ irreducibleComponents Y) :
      topologicalKrullDim V = (d : WithBot ℕ∞) := by
    let c : irreducibleComponents Y := ⟨V, hV⟩
    let x : Y := (genericPoints.ofComponent c).1
    obtain ⟨D, hD, hxD, hDdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
        k Y q x
    have hc : closure ({x} : Set Y) = V := genericPoints.isGenericPoint_ofComponent c
    have hVD : V ⊆ D := by
      rw [← hc]
      exact (isClosed_of_mem_irreducibleComponents D hD).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hxD)
    have hDV : V = D := Set.Subset.antisymm hVD (hV.2 hD.1 hVD)
    rw [hDV, hDdim, hd x]
  exact (hcomponent Z hZ).trans (hcomponent W hW).symm

/-- The local rings of the fibre of a morphism locally of finite type are Noetherian. -/
private instance isNoetherianRing_stalk_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  noetherianStalk_of_locallyNoetherian _ (isLocallyNoetherian_fiber_of_locallyOfFiniteType f _)

/-- Fibre Cohen–Macaulayness at corresponding points of isomorphic arrows of finite type. -/
private theorem fiberCM_iff_arrowIso {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ S')
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (e : Arrow.mk f ≅ Arrow.mk g) (x : X) :
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
      IsCohenMacaulayLocalRing
        ((g.fiber (g (e.hom.left x))).presheaf.stalk (g.asFiber (e.hom.left x))) := by
  have : LocallyOfFiniteType (e.hom.left ≫ g) := inferInstance
  have : LocallyOfFiniteType (f ≫ e.hom.right) := inferInstance
  have hcomp := isLocallyNoetherian_fiber_of_locallyOfFiniteType (e.hom.left ≫ g)
    (g (e.hom.left x))
  have hcomp' := isLocallyNoetherian_fiber_of_locallyOfFiniteType (f ≫ e.hom.right)
    (e.hom.right (f x))
  have : IsNoetherianRing
      (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
        ((f ≫ e.hom.right).asFiber x)) :=
    noetherianStalk_of_locallyNoetherian _ hcomp'
  have : IsNoetherianRing
      (((e.hom.left ≫ g).fiber (g (e.hom.left x))).presheaf.stalk
        ((e.hom.left ≫ g).asFiber x)) :=
    noetherianStalk_of_locallyNoetherian _ hcomp
  have : IsLocalRing
      (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
        ((f ≫ e.hom.right).asFiber x)) := LocallyRingedSpace.isLocalRing _ _
  have : IsLocalRing
      (((e.hom.left ≫ g).fiber (g (e.hom.left x))).presheaf.stalk
        ((e.hom.left ≫ g).asFiber x)) := LocallyRingedSpace.isLocalRing _ _
  exact localFiberCM_iff_arrowIso f g e
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType f)
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType g) x hcomp

private theorem cohenMacaulayAt_resLE
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s))
    (U : S.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (x : V.1.toScheme) :
    Scheme.Hom.IsCohenMacaulayAt (f.resLE U.1 V.1 e)
      (fun s => isLocallyNoetherian_fiber_of_locallyOfFiniteType (f.resLE U.1 V.1 e) s) x := by
  let p := f.resLE U.1 V.1 e
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine U.1.toScheme := U.2
  have : Flat p := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    apply (RingHom.Flat.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U.1 V.1 e)).mpr
    let _ := (f.appLE U.1 V.1 e).hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr (f.flat_appLE U.2 V.2 e)
  let hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) :=
    fun s => isLocallyNoetherian_fiber_of_locallyOfFiniteType f s
  have hCMf : Scheme.Hom.IsCohenMacaulay f hf :=
    (isCohenMacaulay_iff_flat_and_fibers f hf).2 ⟨inferInstance, hCM⟩
  let j : V.1.toScheme ⟶ X := V.1.ι
  have : IsOpenImmersion j := inferInstance
  have : LocallyOfFiniteType j := inferInstance
  let g := j ≫ f
  have : IsNoetherianRing
      (((j ≫ f).fiber (f (j x))).presheaf.stalk ((j ≫ f).asFiber x)) :=
    noetherianStalk_of_locallyNoetherian _
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType g _)
  have : IsLocalRing
      (((j ≫ f).fiber (f (j x))).presheaf.stalk ((j ≫ f).asFiber x)) :=
    LocallyRingedSpace.isLocalRing _ _
  have hCMg : IsCohenMacaulayLocalRing
      (((j ≫ f).fiber (f (j x))).presheaf.stalk ((j ≫ f).asFiber x)) :=
    (localFiberCM_iff_sourceOpenImmersion j f x (hf _)
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType g _)).mp (hCMf (j x)).2
  let E : Arrow.mk (p ≫ U.1.ι) ≅ Arrow.mk g :=
    Arrow.isoMk' (p ≫ U.1.ι) g (Iso.refl _) (Iso.refl _) (by
      simp [p, g, j])
  have : IsNoetherianRing
      (((p ≫ U.1.ι).fiber (U.1.ι (p x))).presheaf.stalk ((p ≫ U.1.ι).asFiber x)) :=
    noetherianStalk_of_locallyNoetherian _
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType (p ≫ U.1.ι) _)
  have : IsLocalRing
      (((p ≫ U.1.ι).fiber (U.1.ι (p x))).presheaf.stalk ((p ≫ U.1.ι).asFiber x)) :=
    LocallyRingedSpace.isLocalRing _ _
  have hCMcomp : IsCohenMacaulayLocalRing
      (((p ≫ U.1.ι).fiber (U.1.ι (p x))).presheaf.stalk
        ((p ≫ U.1.ι).asFiber x)) := by
    simpa [E] using (fiberCM_iff_arrowIso (p ≫ U.1.ι) g E x).mpr hCMg
  have htarget := localFiberCM_iff_openTarget U.1.ι p (p x) x
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType p _)
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType (p ≫ U.1.ι) _)
  change IsFlatAt p.toLRSHom.toShHom x ∧
      IsCohenMacaulayLocalRing ((p.fiber (p x)).presheaf.stalk (p.asFiber x))
  exact ⟨(Flat.iff_flat_stalkMap p).mp inferInstance x, htarget.mpr hCMcomp⟩

private theorem fiberRingCM_chart
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s))
    (U : S.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (x : V.1.toScheme) :
    let p := f.resLE U.1 V.1 e
    let q := (arrowIsoSpecΓOfIsAffine p).hom.left x
    letI : q.asIdeal.IsPrime := q.isPrime
    let R := Γ(U.1.toScheme, ⊤)
    let T := Γ(V.1.toScheme, ⊤)
    letI : Algebra R T := p.appTop.hom.toAlgebra
    Module.IsMaximalCohenMacaulay
      (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
        ((q.asIdeal.under R).map (algebraMap R T)))))
      (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
        ((q.asIdeal.under R).map (algebraMap R T))))) := by
  let p := f.resLE U.1 V.1 e
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine U.1.toScheme := U.2
  let : Algebra Γ(U.1.toScheme, ⊤) Γ(V.1.toScheme, ⊤) := p.appTop.hom.toAlgebra
  let g : Spec (.of Γ(V.1.toScheme, ⊤)) ⟶ Spec (.of Γ(U.1.toScheme, ⊤)) :=
    Spec.map p.appTop
  let E := arrowIsoSpecΓOfIsAffine p
  let q := E.hom.left x
  have : LocallyOfFinitePresentation p := inferInstance
  have : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.SpecMap_iff p.appTop |>.mpr p.finitePresentation_appTop
  have : (q.asIdeal).IsPrime := q.isPrime
  have hCMp := cohenMacaulayAt_resLE f hCM U V e x
  have hCMg : IsCohenMacaulayLocalRing
      ((g.fiber (g q)).presheaf.stalk (g.asFiber q)) :=
    (fiberCM_iff_arrowIso p g E x).mp hCMp.2
  exact (CohenMacaulayFiber.fiberLocalRing_isMaximalCohenMacaulay_iff
    (hf := isLocallyNoetherian_fiber_of_locallyOfFiniteType g) q).mp hCMg

private lemma fiberDimensionAt_specMap_hom {R B : CommRingCat.{u}}
    (φ : R ⟶ B) (x : Spec B) [x.asIdeal.IsPrime] :
    topologicalKrullDimAt
        ((Spec.map φ).fiber ((Spec.map φ) x)) ((Spec.map φ).asFiber x) =
      (letI := φ.hom.toAlgebra
       Algebra.relativeDimensionAt R x.asIdeal) := by
  let _ := φ.hom.toAlgebra
  rw [topologicalKrullDimAt_eq_of_homeomorph ((Spec.map φ).fiberHomeo _) _]
  unfold Algebra.relativeDimensionAt
  congr 1
  exact Subtype.ext ((Spec.map φ).fiberι_asFiber x)

private theorem fiberDimensionAt_resLE_eq_relativeDimensionAt
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (x : V.1.toScheme) :
    topologicalKrullDimAt (f.fiber (f (V.1.ι x))) (f.asFiber (V.1.ι x)) =
    let p := f.resLE U.1 V.1 e
    let E := arrowIsoSpecΓOfIsAffine p
    let q := E.hom.left x
    letI : q.asIdeal.IsPrime := q.isPrime
    letI := p.appTop.hom.toAlgebra
    Algebra.relativeDimensionAt (Γ(U.1.toScheme, ⊤)) q.asIdeal := by
  let p := f.resLE U.1 V.1 e
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine U.1.toScheme := U.2
  let : Algebra Γ(U.1.toScheme, ⊤) Γ(V.1.toScheme, ⊤) := p.appTop.hom.toAlgebra
  let φ := p.appTop
  let g := Spec.map φ
  let E := arrowIsoSpecΓOfIsAffine p
  have : IsOpenImmersion E.hom.left := inferInstance
  have : IsOpenImmersion E.hom.right := inferInstance
  have h₁ := fiberDimensionAt_comp_embedding p E.hom.right
    E.hom.right.isOpenEmbedding.injective x
  let K (m : V.1.toScheme ⟶ Spec (.of Γ(U.1.toScheme, ⊤))) : WithBot ℕ∞ :=
    topologicalKrullDimAt (m.fiber (m x)) (m.asFiber x)
  have h₂ : K (p ≫ E.hom.right) = K (E.hom.left ≫ g) :=
    (congrArg K E.hom.w).symm
  have h₃ := fiberDimensionAt_comp_openImmersion E.hom.left g x
  have hIso : topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) =
      topologicalKrullDimAt (g.fiber (g (E.hom.left x))) (g.asFiber (E.hom.left x)) :=
    h₁.symm.trans (h₂.trans h₃)
  let j := V.1.ι
  have h₄ := fiberDimensionAt_comp_openImmersion j f x
  have h₅ := fiberDimensionAt_comp_embedding p U.1.ι
    U.1.ι.isOpenEmbedding.injective x
  have h₆ : topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) =
      topologicalKrullDimAt (f.fiber (f (V.1.ι x))) (f.asFiber (V.1.ι x)) := by
    calc
      topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) =
          topologicalKrullDimAt ((p ≫ U.1.ι).fiber ((p ≫ U.1.ι) x))
          ((p ≫ U.1.ι).asFiber x) := h₅.symm
      _ = topologicalKrullDimAt ((j ≫ f).fiber ((j ≫ f) x)) ((j ≫ f).asFiber x) := by
        rw [Scheme.Hom.resLE_comp_ι]
      _ = topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := h₄
      _ = topologicalKrullDimAt (f.fiber (f (V.1.ι x))) (f.asFiber (V.1.ι x)) := rfl
  have : (E.hom.left x).asIdeal.IsPrime := (E.hom.left x).isPrime
  have hSpec := fiberDimensionAt_specMap_hom φ (E.hom.left x)
  exact h₆.symm.trans (hIso.trans hSpec)

private lemma exists_nat_fiberDimensionAt {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    ∃ n : ℕ, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ((n : ℕ) : WithBot ℕ∞) := by
  have hc : ∃ U : S.affineOpens, ∃ V : X.affineOpens,
      ∃ e : V.1 ≤ f ⁻¹ᵁ U.1, V.1 ≤ ⊤ ∧ x ∈ V.1 := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    have hxWU : x ∈ (⊤ : Set X) ∩ f ⁻¹' (U : Set S) := ⟨Set.mem_univ _, hxU⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxWU
        (isOpen_univ.inter (U.2.preimage f.continuous))
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hVWU.trans inf_le_right,
      hVWU.trans inf_le_left, hxV⟩
  obtain ⟨U', V', hVU, hVtop, hxV⟩ := hc
  let _ := (f.appLE U'.1 V'.1 hVU).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, U'.1) Γ(X, V'.1) :=
    f.finitePresentation_appLE U'.2 V'.2 hVU
  let q := V'.2.primeIdealOf ⟨x, hxV⟩
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨n, hn⟩ := Algebra.exists_relativeDimensionAt_eq_natCast
    Γ(S, U'.1) q.asIdeal
  refine ⟨n, ?_⟩
  rw [fiberDimensionAt_eq_relativeDimensionAt_chart f U' V' hVU x hxV]
  exact hn

private noncomputable def fiberDimensionNat {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) : ℕ :=
  Classical.choose (exists_nat_fiberDimensionAt f x)

private theorem fiberDimensionNat_spec {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ((fiberDimensionNat f x : ℕ) : WithBot ℕ∞) :=
  by simpa only [fiberDimensionNat] using Classical.choose_spec (exists_nat_fiberDimensionAt f x)

/-- The locally constant function giving the relative dimension of a flat, locally finitely
presented morphism with Cohen–Macaulay fibres. -/
@[stacks 02NM "relative dimension function"]
public noncomputable def relativeDimensionFunction
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) : LocallyConstant X ℕ := by
  refine ⟨fiberDimensionNat f, ?_⟩
  refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
  intro d
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hc : ∃ U : S.affineOpens, ∃ V : X.affineOpens,
      ∃ e : V.1 ≤ f ⁻¹ᵁ U.1, V.1 ≤ ⊤ ∧ x ∈ V.1 := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    have hxWU : x ∈ (⊤ : Set X) ∩ f ⁻¹' (U : Set S) := ⟨Set.mem_univ _, hxU⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxWU
        (isOpen_univ.inter (U.2.preimage f.continuous))
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hVWU.trans inf_le_right,
      hVWU.trans inf_le_left, hxV⟩
  obtain ⟨U, V, hVU, hVtop, hxV⟩ := hc
  let p := f.resLE U.1 V.1 hVU
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine U.1.toScheme := U.2
  have : Flat p := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    apply (RingHom.Flat.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U.1 V.1 hVU)).mpr
    let _ := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr (f.flat_appLE U.2 V.2 hVU)
  have : LocallyOfFinitePresentation p := inferInstance
  let R := Γ(U.1.toScheme, ⊤)
  let T := Γ(V.1.toScheme, ⊤)
  let : Algebra R T := p.appTop.hom.toAlgebra
  let E := arrowIsoSpecΓOfIsAffine p
  let O : Set (PrimeSpectrum T) := {q |
    Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T)))))
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T))))) ∧
      Algebra.relativeDimensionAt R q.asIdeal = d}
  have : Module.Flat R T :=
    RingHom.flat_algebraMap_iff.mp p.flat_appTop
  have : Algebra.FinitePresentation R T :=
    RingHom.finitePresentation_algebraMap.mp p.finitePresentation_appTop
  have hO : IsOpen O := Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq
    R T d
  let W : Set V.1.toScheme := E.hom.left ⁻¹' O
  have hW : IsOpen W := hO.preimage (Scheme.Hom.continuous E.hom.left)
  let A : Set X := V.1.ι.base '' W
  have hA : IsOpen A := V.1.ι.isOpenEmbedding.isOpenMap W hW
  refine ⟨A, ?_, hA, ?_⟩
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    let q : PrimeSpectrum T := E.hom.left z
    let : q.asIdeal.IsPrime := q.isPrime
    have hNat : fiberDimensionNat f (V.1.ι z) = d := by
      have hcast : (fiberDimensionNat f (V.1.ι z) : WithBot ℕ∞) =
          (d : WithBot ℕ∞) := by
        calc
          _ = topologicalKrullDimAt (f.fiber (f (V.1.ι z)))
              (f.asFiber (V.1.ι z)) := (fiberDimensionNat_spec f (V.1.ι z)).symm
          _ = Algebra.relativeDimensionAt R q.asIdeal := by
            simpa [q, R, T, E] using
              fiberDimensionAt_resLE_eq_relativeDimensionAt f U V hVU z
          _ = (d : WithBot ℕ∞) := by exact_mod_cast hz.2
      exact_mod_cast hcast
    exact hNat
  · let z : V.1.toScheme := ⟨x, hxV⟩
    let q : PrimeSpectrum T := E.hom.left z
    let : q.asIdeal.IsPrime := q.isPrime
    have hCMq := fiberRingCM_chart f hCM U V hVU z
    have hNat : fiberDimensionNat f (V.1.ι z) = d := by
      simpa [z] using hx
    have hRel : Algebra.relativeDimensionAt R q.asIdeal = d := by
      have hcast : (fiberDimensionNat f (V.1.ι z) : WithBot ℕ∞) =
          (d : WithBot ℕ∞) := by exact_mod_cast hNat
      have hcomp : topologicalKrullDimAt (f.fiber (f (V.1.ι z)))
          (f.asFiber (V.1.ι z)) = Algebra.relativeDimensionAt R q.asIdeal := by
        simpa [q, R, T, E] using
          fiberDimensionAt_resLE_eq_relativeDimensionAt f U V hVU z
      have hrelcast : Algebra.relativeDimensionAt R q.asIdeal =
          (fiberDimensionNat f (V.1.ι z) : WithBot ℕ∞) :=
        hcomp.symm.trans (fiberDimensionNat_spec f (V.1.ι z))
      exact hrelcast.trans hcast
    have hz : z ∈ W := by
      change q ∈ O
      exact ⟨hCMq, hRel⟩
    refine ⟨z, hz, ?_⟩
    rfl

/-- At a point, the relative dimension function is the local Krull dimension of its fibre. -/
@[stacks 02NM "pointwise relative dimension"]
public theorem relativeDimensionFunction_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ((relativeDimensionFunction f hCM x : ℕ) : WithBot ℕ∞) := by
  unfold relativeDimensionFunction
  change topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
    ((fiberDimensionNat f x : ℕ) : WithBot ℕ∞)
  exact fiberDimensionNat_spec f x

/-- The canonical open subscheme where the relative dimension is `d`. -/
@[stacks 02NM "canonical dimension pieces"]
public def relativeDimensionOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) (d : ℕ) : X.Opens :=
  ⟨{x | relativeDimensionFunction f hCM x = d},
    (relativeDimensionFunction f hCM).isLocallyConstant.isOpen_fiber d⟩

/-- Every canonical relative-dimension piece is open and closed. -/
@[stacks 02NM "canonical pieces are clopen"]
public theorem relativeDimensionOpen_isClopen
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) (d : ℕ) :
    IsClopen (relativeDimensionOpen f hCM d : Set X) := by
  refine ⟨?_, (relativeDimensionFunction f hCM).isLocallyConstant.isOpen_fiber d⟩
  · rw [← isOpen_compl_iff]
    convert isOpen_iUnion (fun n : {n : ℕ // n ≠ d} =>
      (relativeDimensionFunction f hCM).isLocallyConstant.isOpen_fiber n) using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨⟨relativeDimensionFunction f hCM x, ?_⟩, rfl⟩
      intro h
      exact hx h
    · rintro ⟨⟨n, hn⟩, hx⟩ h
      exact hn (hx.symm.trans h)

/-- The canonical relative-dimension pieces cover the source. -/
@[stacks 02NM "canonical pieces cover"]
public theorem iSup_relativeDimensionOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) :
    ⨆ d : ℕ, relativeDimensionOpen f hCM d = ⊤ := by
  ext x
  rw [Opens.coe_iSup]
  simp only [Set.mem_iUnion]
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨relativeDimensionFunction f hCM x, rfl⟩

/-- Distinct canonical relative-dimension pieces are disjoint. -/
@[stacks 02NM "canonical pieces are disjoint"]
public theorem pairwise_disjoint_relativeDimensionOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) :
    Pairwise (Disjoint on relativeDimensionOpen f hCM) := by
  intro d d' hne
  change Disjoint (relativeDimensionOpen f hCM d) (relativeDimensionOpen f hCM d')
  apply TopologicalSpace.Opens.coe_disjoint.mp
  rw [Set.disjoint_left]
  intro x hx hx'
  change relativeDimensionFunction f hCM x = d at hx
  change relativeDimensionFunction f hCM x = d' at hx'
  exact hne (hx.symm.trans hx')

/-- The restriction of the morphism to its `d`-dimensional locus has relative dimension `d`. -/
@[stacks 02NM "canonical pieces have pure relative dimension"]
public theorem relativeDimensionOpen_relativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) (d : ℕ) :
    RelativeDimension ((relativeDimensionOpen f hCM d).ι ≫ f) d := by
  let U := relativeDimensionOpen f hCM d
  let g := U.ι ≫ f
  let : LocallyOfFiniteType g := inferInstance
  intro s hs
  have hdim : ∀ y : g.fiber s,
      topologicalKrullDimAt (g.fiber s) y = (d : WithBot ℕ∞) := by
    intro y
    let x : U.toScheme := g.fiberι s y
    have hsx : g x = s := g.apply_fiberι s y
    have hsets : g ⁻¹' {s} = g ⁻¹' {g x} := by rw [hsx]
    let e : g.fiber s ≃ₜ g.fiber (g x) :=
      (g.fiberHomeo s).trans
        ((Homeomorph.setCongr hsets).trans (g.fiberHomeo (g x)).symm)
    have hey : e y = g.asFiber x := by
      apply (g.fiberι (g x)).isEmbedding.injective
      rfl
    have hedim := topologicalKrullDimAt_eq_of_homeomorph e y
    have hcomp := fiberDimensionAt_comp_openImmersion U.ι f x
    have hxU : (U.ι x) ∈ (relativeDimensionOpen f hCM d : Set X) := x.property
    have hvalue : relativeDimensionFunction f hCM (U.ι x) = d := hxU
    have hspec := relativeDimensionFunction_apply f hCM (U.ι x)
    have hlocal : topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) =
        (d : WithBot ℕ∞) := by
      exact hcomp.trans
        (hspec.trans (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hvalue))
    exact hedim.trans (congrArg (topologicalKrullDimAt (g.fiber (g x))) hey).symm |>.trans hlocal
  refine ⟨?_, ?_⟩
  · let : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
      Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField g s
    apply equidimensional_of_constant_fiber_local_dimension
      (S.residueField s) (g.fiber s) (g.fiberToSpecResidueField s)
    exact hdim
  · let : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
      Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField g s
    let : Nonempty (g.fiber s) := hs
    have hglobal : topologicalKrullDim (g.fiber s) =
        ⨆ y : g.fiber s, topologicalKrullDimAt (g.fiber s) y := by
      rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
      simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    rw [hglobal]
    simp only [hdim, iSup_const]

/-- **Stacks Project, Tag 02NM.** A flat morphism locally of finite presentation with
Cohen–Macaulay fibres is the disjoint union of clopen subschemes of pure relative dimension. -/
@[stacks 02NM]
public theorem exists_clopen_relativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) :
    ∃ U : ℕ → X.Opens,
      (∀ d : ℕ, IsClopen (U d : Set X)) ∧
      (iSup U = ⊤) ∧
      Pairwise (Disjoint on U) ∧
      (∀ d : ℕ, RelativeDimension ((U d).ι ≫ f) d) :=
  ⟨relativeDimensionOpen f hCM, relativeDimensionOpen_isClopen f hCM,
    iSup_relativeDimensionOpen f hCM, pairwise_disjoint_relativeDimensionOpen f hCM,
    relativeDimensionOpen_relativeDimension f hCM⟩

end AlgebraicGeometry

end
