module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.Topology.Sober.Generization

/-!
# Étale morphisms over a normal scheme with separably closed function field

Let `X` be an integral normal scheme whose function field is separably closed. A separated
étale morphism to `X` is a disjoint union of open immersions, and every local ring of `X` is
strictly henselian.

## Main results

* `AlgebraicGeometry.exists_coproduct_open_immersions`: a separated étale morphism to `X` is
  isomorphic over `X` to a coproduct of open immersions.
* `AlgebraicGeometry.stalk_strictlyHenselian`: every local ring of `X` is strictly henselian.

## References

* [Stacks Project, Tag 09Z9](https://stacks.math.columbia.edu/tag/09Z9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of a quasi-sober space with no proper generalization is a generic point. -/
private lemma mem_genericPoints_of_forall_generalization_eq
    {T : Type*} [TopologicalSpace T] [QuasiSober T] (x : T)
    (h : ∀ x' : T, Specializes x' x → x' = x) : x ∈ genericPoints T := by
  let Z : irreducibleComponents T :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  rw [← h _ ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)]
  exact (genericPoints.ofComponent Z).2

/-- A point whose image under an injective continuous map is generic is itself generic. -/
private lemma genericPoints_of_injective_continuous
    {T S : Type*} [TopologicalSpace T] [TopologicalSpace S]
    [T0Space S] [QuasiSober T]
    (f : T → S) (hf : Function.Injective f) (hfc : Continuous f) (x : T)
    (hgen : f x ∈ genericPoints S) : x ∈ genericPoints T :=
  mem_genericPoints_of_forall_generalization_eq x fun _ hy ↦
    hf (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hgen _ (hy.map hfc))

/-- A generic point of a scheme is a generic point of the fibre of a morphism through
it. -/
private lemma genericPoint_mem_fiber_of_genericPoint
    {X S : Scheme} (f : X ⟶ S) (x : X) (hx : x ∈ genericPoints X)
    (η : S) (hη : f x = η) :
    (f.fiberHomeo η).symm ⟨x, by simp [hη]⟩ ∈ genericPoints (f.fiber η) := by
  apply genericPoints_of_injective_continuous (f.fiberι η)
    (f.fiberι η).isEmbedding.injective (f.fiberι η).continuous
  simpa [Scheme.Hom.fiberι_fiberHomeo_symm] using hx

/-- The residue-field map of an unramified morphism of finite type is an isomorphism at a
point whose image has separably closed residue field. -/
private theorem residueFieldMap_isIso_of_isSepClosed
    {X Y : Scheme.{u}} (f : Y ⟶ X) [FormallyUnramified f]
    [LocallyOfFiniteType f] (ξ : Y) [IsSepClosed (X.residueField (f ξ))] :
    IsIso (f.residueFieldMap ξ) := by
  let : Algebra (X.residueField (f ξ)) (Y.residueField ξ) :=
    (f.residueFieldMap ξ).hom.toAlgebra
  let : Algebra.IsSeparable (X.residueField (f ξ)) (Y.residueField ξ) := inferInstance
  apply (ConcreteCategory.isIso_iff_bijective (f.residueFieldMap ξ)).mpr
  simpa only [RingHom.algebraMap_toAlgebra] using
    (IsSepClosed.algebraMap_bijective (X.residueField (f ξ)) (Y.residueField ξ))

/-- Over an integral scheme with separably closed function field, the residue-field map of an
étale morphism is an isomorphism at every generic point. -/
private theorem etale_residueFieldMap_isIso_at_genericPoints
    {X Y : Scheme.{u}} [IsIntegral X] [IsSepClosed X.functionField]
    (f : Y ⟶ X) [Etale f] (ξ : Y) (hξ : ξ ∈ genericPoints Y) :
    IsIso (f.residueFieldMap ξ) := by
  have hξX : f ξ = genericPoint X := by
    simpa [genericPoints_eq_singleton] using
      (genericPoints_map_of_generalizingMap f (Flat.generalizingMap f) hξ)
  have : IsSepClosed (X.residueField (f ξ)) := by
    rw [hξX]
    exact IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩).symm
  exact residueFieldMap_isIso_of_isSepClosed f ξ

/-- A space with a finite open cover by subspaces of finitely many irreducible components has
finitely many irreducible components. -/
private theorem finite_irreducibleComponents_of_finite_open_cover
    (T : Type*) [TopologicalSpace T]
    (ι : Type*) [Finite ι] (U : ι → Opens T)
    (hcover : (Set.univ : Set T) ⊆ ⋃ i, (U i : Set T))
    (hfin : ∀ i, (irreducibleComponents (U i)).Finite) :
    (irreducibleComponents T).Finite := by
  classical
  let (i : ι) : Finite (irreducibleComponents (U i)) := Set.finite_coe_iff.mp (hfin i)
  have chooseIndex : ∀ Z : irreducibleComponents T, ∃ i : ι,
      (Z.1 ∩ (U i : Set T)).Nonempty := by
    intro Z
    obtain ⟨x, hx⟩ := Z.2.1.nonempty
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    exact ⟨i, ⟨x, hx, hi⟩⟩
  choose i hi using chooseIndex
  have hclosure (Z : irreducibleComponents T) (j : ι)
      (h : (Z.1 ∩ (U j : Set T)).Nonempty) :
      closure ((Subtype.val : U j → T) '' (Subtype.val ⁻¹' Z.1)) = Z.1 :=
    closure_image_preimage_of_isPreirreducible
      (Subtype.val : U j → T) (U j).isOpenEmbedding'.isOpenMap Z.1
      (by obtain ⟨x, hx, hxU⟩ := h; exact ⟨⟨x, hxU⟩, hx⟩)
      Z.2.1.2 (isClosed_of_mem_irreducibleComponents _ Z.2)
  let q : irreducibleComponents T → Σ i : ι, irreducibleComponents (U i) := fun Z ↦
    ⟨i Z, ⟨Subtype.val ⁻¹' Z.1, preimage_mem_irreducibleComponents Z.2
      (U (i Z)).isOpenEmbedding' (by simpa using hi Z)⟩⟩
  apply Set.finite_coe_iff.mpr (Finite.of_injective q ?_)
  intro Z W h
  apply Subtype.ext
  have h' := congrArg (fun a : Σ i : ι, irreducibleComponents (U i) ↦
    closure ((Subtype.val : U a.1 → T) '' a.2.1)) h
  simpa only [q, hclosure Z (i Z) (hi Z), hclosure W (i W) (hi W)] using h'

/-- A quasi-compact scheme flat and locally of finite type over a base whose compact opens
have finitely many irreducible components has finitely many generic points. -/
private theorem finite_genericPoints_of_flat_locallyOfFiniteType_quasiCompact
    {T S : Scheme} (f : T ⟶ S) [QuasiCompact f] [Flat f]
    [LocallyOfFiniteType f] (hS : (irreducibleComponents S).Finite) :
    (genericPoints T).Finite := by
  classical
  let : Finite (genericPoints S) := genericPoints.finite hS
  have hfg : ∀ η : genericPoints S, (genericPoints (f.fiber η.1)).Finite := by
    intro η
    let : LocallyOfFiniteType (f.fiberToSpecResidueField η.1) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
      infer_instance
    let : IsLocallyNoetherian (f.fiber η.1) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η.1)
    let : IsNoetherian (f.fiber η.1) := AlgebraicGeometry.IsNoetherian.mk
    exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  let (η : genericPoints S) : Finite (genericPoints (f.fiber η.1)) := hfg η
  have hmap (η : genericPoints T) : f η.1 ∈ genericPoints S :=
    genericPoints_map_of_generalizingMap f (Flat.generalizingMap f) η.2
  let g : genericPoints T → Σ η : genericPoints S, genericPoints (f.fiber η.1) := fun x ↦
    let η : genericPoints S := ⟨f x.1, hmap x⟩
    ⟨η, ⟨(f.fiberHomeo η.1).symm ⟨x.1, by simp [η]⟩,
      genericPoint_mem_fiber_of_genericPoint f x.1 x.2 η.1 rfl⟩⟩
  apply Finite.of_injective g
  intro x y h
  apply Subtype.ext
  simpa [g, Scheme.Hom.fiberι_fiberHomeo_symm] using
    congrArg (fun z : Σ η : genericPoints S, genericPoints (f.fiber η.1) ↦
      f.fiberι z.1.1 z.2.1) h

/-- Every compact open of a scheme flat and locally of finite type over such a base has
finitely many irreducible components. -/
@[ega "IV 4.4.1" "partial"]
private theorem finite_irreducibleComponents_of_flat_locallyOfFiniteType
    {T S : Scheme} (f : T ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (hS : ∀ V : S.Opens, IsCompact (V : Set S) →
      (irreducibleComponents V).Finite) :
    ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite := by
  intro U hU
  classical
  let W : Scheme := U.toScheme
  let g : W ⟶ S := U.ι ≫ f
  let I := {p : S.affineOpens × W.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1}
  let A (i : I) : W.Opens := i.1.2.1
  have hcover : (Set.univ : Set W) ⊆ ⋃ i : I, (A i : Set W) := by
    intro x hx
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    let V : S.affineOpens := ⟨V₀, hV₀⟩
    obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZW⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ g ⁻¹ᵁ V.1 from hxV) (V.1.isOpen.preimage g.continuous)
    let i : I := ⟨(V, ⟨Z, hZ⟩), hZW⟩
    exact Set.mem_iUnion.mpr ⟨i, hxZ⟩
  let : CompactSpace W := isCompact_iff_compactSpace.mp (by simpa [W] using hU)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : I ↦ (A i : Set W)) (fun i ↦ (A i).isOpen) hcover
  let J := {i : I // i ∈ t}
  let A' (i : J) : W.Opens := A i.1
  have hcover' : (Set.univ : Set W) ⊆ ⋃ i : J, (A' i : Set W) := by
    intro x hx
    obtain ⟨i, hit, hix⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hix⟩
  have hfin' : ∀ i : J, (irreducibleComponents (A' i).toScheme).Finite := by
    intro i
    let V : S.affineOpens := i.1.1.1
    let Z : W.affineOpens := i.1.1.2
    let hZV : Z.1 ≤ g ⁻¹ᵁ V.1 := i.1.2
    let q := g.resLE V.1 Z.1 hZV
    have hV : (irreducibleComponents V.1).Finite := hS V.1 (by simpa using V.2.isCompact)
    have : Flat q := by dsimp [q]; infer_instance
    have : LocallyOfFiniteType q := by dsimp [q]; infer_instance
    let : Finite (genericPoints (A' i).toScheme) :=
      finite_genericPoints_of_flat_locallyOfFiniteType_quasiCompact q hV
    exact Finite.of_equiv (genericPoints (A' i).toScheme)
      (genericPoints.equiv (α := (A' i).toScheme))
  simpa [W] using
    (finite_irreducibleComponents_of_finite_open_cover W J A' hcover'
      (fun i ↦ by change (irreducibleComponents (A' i).toScheme).Finite; exact hfin' i))

/-- A separated étale morphism to an integral normal scheme with separably closed function field
is a disjoint union of open immersions. -/
@[stacks 09Z9 "part (1)"]
theorem exists_coproduct_open_immersions
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (U : Scheme.{u}) (f : U ⟶ X) [Etale f] [IsSeparated f] :
    ∃ (I : Type u) (V : I → Scheme.{u}) (j : ∀ i, V i ⟶ X)
      (_ : ∀ i, IsOpenImmersion (j i)) (e : U ≅ ∐ V),
      e.hom ≫ Sigma.desc j = f := by
  classical
  let : IsNormal U := isNormal_of_etale f
  have hXcomp : ∀ W : X.Opens, IsCompact (W : Set X) →
      (irreducibleComponents W).Finite := by
    intro W hW
    by_cases hne : Nonempty W
    · let : Nonempty W := hne
      let : IsIntegral W := inferInstance
      simp [irreducibleComponents_eq_singleton]
    · let : IsEmpty W := ⟨fun x ↦ hne ⟨x⟩⟩
      exact Set.finite_univ.subset (Set.subset_univ _)
  have hUcomp : ∀ W : U.Opens, IsCompact (W : Set U) →
      (irreducibleComponents W).Finite :=
    finite_irreducibleComponents_of_flat_locallyOfFiniteType f hXcomp
  obtain ⟨I, V, hVnormal, hVintegral, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct hUcomp).mp (inferInstance : IsNormal U)
  let j (i : I) : V i ⟶ X := Sigma.ι V i ≫ e.inv ≫ f
  refine ⟨I, V, j, ?_, e, ?_⟩
  · intro i
    let : IsIntegral (V i) := hVintegral i
    let : IsOpenImmersion (Sigma.ι V i ≫ e.inv) := inferInstance
    let : Etale (j i) := inferInstance
    let : IsSeparated (j i) := inferInstance
    apply isOpenImmersion_of_etale_of_separated_of_genericPoints_injOn
    · intro ξ hξ
      exact etale_residueFieldMap_isIso_at_genericPoints (j i) ξ hξ
    · intro ξ hξ ζ hζ hEq
      simp only [genericPoints_eq_singleton, Set.mem_singleton_iff] at hξ hζ
      exact hξ.trans hζ.symm
  · apply (cancel_epi e.inv).1
    apply Sigma.hom_ext
    intro i
    simp [j]

/-- Every local ring of an integral normal scheme with separably closed function field is
strictly henselian. -/
@[stacks 09Z9 "part (2)"]
instance stalk_strictlyHenselian
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField] (x : X) :
    _root_.StrictlyHenselianLocalRing (X.presheaf.stalk x) := by
  let : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  have h := normal_local_domain_sepClosed_fractionField_isStrictlyHenselian
    (X.presheaf.stalk x) X.functionField
  let : HenselianLocalRing (X.presheaf.stalk x) := h.1
  let : IsSepClosed (IsLocalRing.ResidueField (X.presheaf.stalk x)) := h.2
  exact _root_.StrictlyHenselianLocalRing.mk

end AlgebraicGeometry

end
