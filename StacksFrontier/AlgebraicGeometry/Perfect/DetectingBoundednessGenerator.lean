module

public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedAboveGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.BoundednessStandardModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.GlobalDerivedHomOnASpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual

/-!
# Detecting boundedness with a perfect generator

Let `X` be a quasi-compact and quasi-separated scheme, let `G` be a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)`, and let `E` be an object of `D_QCoh(𝒪_X)`. Then the following are
equivalent:

1. `E ∈ D^-_QCoh(𝒪_X)`,
2. `Hom_{D(𝒪_X)}(G[-i], E) = 0` for `i ≫ 0`,
3. `Ext^i_X(G, E) = 0` for `i ≫ 0`,
4. `RHom_X(G, E)` is in `D^-(ℤ)`,
5. `H^i(X, G^∨ ⊗^L E) = 0` for `i ≫ 0`,
6. `RΓ(X, G^∨ ⊗^L E)` is in `D^-(ℤ)`,
7. for every perfect object `P` of `D(𝒪_X)`, (a) the assertions (2), (3), (4) hold with `G`
   replaced by `P`, (b) `H^i(X, P ⊗^L E) = 0` for `i ≫ 0`, and (c) `RΓ(X, P ⊗^L E)` is in
   `D^-(ℤ)`,

and the same with `D^+`, `i ≪ 0` and `D^+(ℤ)` in place of `D^-`, `i ≫ 0` and `D^-(ℤ)`.

## Main results

* `Stacks.SheafOfModules.minus_of_eventually_subsingleton_shiftedHom`: (2) ⟹ (1) for `D^-`.
* `Stacks.SheafOfModules.plus_of_eventually_subsingleton_shiftedHom`: (2) ⟹ (1) for `D^+`.
* `Stacks.SheafOfModules.tfae_minus_of_isPerfect_generator`: the equivalence of (1) to (7) for
  `D^-`.
* `Stacks.SheafOfModules.tfae_plus_of_isPerfect_generator`: the equivalence of (1) to (7) for
  `D^+`.

## References

* [Stacks Project, Proposition 36.40.5 (Tag 0GEN)](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Proposition 36.40.6 (Tag 0GEQ)](https://stacks.math.columbia.edu/tag/0GEQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry Filter
open Stacks.Cohomology.ModuleSections
open Stacks.Duality.CompactBoundedness (Bdd)

namespace Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-! ### Reformulations -/

section Reformulations

omit [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- `Hom(P⟦-i⟧, E)` vanishes exactly when `Ext^i(P, E)` does. -/
theorem subsingleton_shiftedHom_iff_ext (P E : DerivedCategory (StructureSheafModules X.sheaf))
    (i : ℤ) : Subsingleton (P⟦-i⟧ ⟶ E) ↔ Subsingleton (DerivedCategory.Ext P E i) :=
  ((shiftEquiv' (DerivedCategory (StructureSheafModules X.sheaf)) (-i) i
    (by omega)).toAdjunction.homEquiv P E).subsingleton_congr

omit [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- `E ∈ D^-(𝒪_X)` exactly when its cohomology sheaves vanish in all large degrees. -/
theorem minus_iff_bdd (E : DerivedCategory (StructureSheafModules X.sheaf)) :
    (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).minus E ↔
      Bdd atTop E :=
  (DerivedCategory.minus_iff E).trans eventually_atTop.symm

omit [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- `E ∈ D^+(𝒪_X)` exactly when its cohomology sheaves vanish in all small degrees. -/
theorem plus_iff_bdd (E : DerivedCategory (StructureSheafModules X.sheaf)) :
    (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).plus E ↔
      Bdd atBot E :=
  (DerivedCategory.plus_iff E).trans eventually_atBot.symm

/-- Perfectness at the ringed site of opens is perfectness of the ringed space. -/
theorem isPerfectStd_of_isPerfect (P : DerivedCategory (StructureSheafModules X.sheaf))
    (hP : (ringedSite X.sheaf).IsPerfect P) :
    Stacks.Duality.CompactBoundedness.IsPerfectStd (X := X) P :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace P hP

end Reformulations

/-! ### The two geometric implications -/

section Geometric

/-- On a quasi-compact quasi-separated scheme, if `E ∈ D^-_QCoh(𝒪_X)` and `P` is perfect, then
`Hom(P⟦-i⟧, E) = 0` for `i ≫ 0`. -/
theorem eventually_subsingleton_shiftedHom_of_minus
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (P E : DerivedCategory (StructureSheafModules X.sheaf))
    (hP : (ringedSite X.sheaf).IsPerfect P)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (h : (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).minus E) :
    ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E) :=
  eventually_atTop.1 <|
    Stacks.Duality.CompactBoundedness.eventuallyOrthogonal_of_isPerfect_of_bdd (X := X)
      (Or.inl rfl) P E (isPerfectStd_of_isPerfect P hP) hE ((minus_iff_bdd E).1 h)

/-- On a quasi-compact quasi-separated scheme, if `E ∈ D^+_QCoh(𝒪_X)` and `P` is perfect, then
`Hom(P⟦-i⟧, E) = 0` for `i ≪ 0`. -/
theorem eventually_subsingleton_shiftedHom_of_plus'
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (P E : DerivedCategory (StructureSheafModules X.sheaf))
    (hP : (ringedSite X.sheaf).IsPerfect P)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (h : (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).plus E) :
    ∃ N : ℤ, ∀ i ≤ N, Subsingleton (P⟦-i⟧ ⟶ E) :=
  eventually_atBot.1 <|
    Stacks.Duality.CompactBoundedness.eventuallyOrthogonal_of_isPerfect_of_bdd (X := X)
      (Or.inr rfl) P E (isPerfectStd_of_isPerfect P hP) hE ((plus_iff_bdd E).1 h)

/-- Let `X` be a quasi-compact and quasi-separated scheme, `G` a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)` and `E` an object of `D_QCoh(𝒪_X)`. If `Hom(G⟦-i⟧, E) = 0` for
`i ≫ 0`, then `E ∈ D^-_QCoh(𝒪_X)`. -/
theorem minus_of_eventually_subsingleton_shiftedHom
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (h : ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (G⟦-i⟧ ⟶ E)) :
    (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).minus E :=
  (minus_iff_bdd E).2 <|
    Stacks.Duality.CompactBoundedness.bdd_of_eventuallyOrthogonal_of_isPerfect_generator (X := X)
      (Or.inl rfl) G E (isPerfectStd_of_isPerfect G hG) hgen hE (eventually_atTop.2 h)

/-- Let `X` be a quasi-compact and quasi-separated scheme, `G` a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)` and `E` an object of `D_QCoh(𝒪_X)`. If `Hom(G⟦-i⟧, E) = 0` for
`i ≪ 0`, then `E ∈ D^+_QCoh(𝒪_X)`. -/
theorem plus_of_eventually_subsingleton_shiftedHom
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (h : ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ E)) :
    (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).plus E :=
  (plus_iff_bdd E).2 <|
    Stacks.Duality.CompactBoundedness.bdd_of_eventuallyOrthogonal_of_isPerfect_generator (X := X)
      (Or.inr rfl) G E (isPerfectStd_of_isPerfect G hG) hgen hE (eventually_atBot.2 h)

end Geometric

/-! ### The clause equivalences for an arbitrary perfect object -/

section Clauses

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]

/-- `Ext^i_X(P, E)` vanishes exactly when `H^i(RHom_X(P, E))` does. -/
theorem subsingleton_ext_iff_isZero_homology_globalDerivedHom
    (P E : DerivedCategory (StructureSheafModules X.sheaf)) (i : ℤ) :
    Subsingleton (DerivedCategory.Ext P E i) ↔
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
          (((globalDerivedHom X.sheaf).obj (op P)).obj E))) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have e : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
        (((globalDerivedHom X.sheaf).obj (op P)).obj E)) : Type u) ≃+ (P ⟶ E⟦i⟧) :=
    RingedSite.globalDerivedHomModulesDegreeEquiv (ringedSite X.sheaf) P E i
  exact e.toEquiv.subsingleton_congr.symm

variable [∀ V : Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- `Ext^i_X(Q, E)` vanishes exactly when `H^i(X, Q^∨ ⊗^L E)` does, for a perfect `Q`. -/
theorem subsingleton_ext_iff_isZero_homology_dual_tensor
    (Q E : DerivedCategory (StructureSheafModules X.sheaf))
    (hQ : (ringedSite X.sheaf).IsPerfect Q) (i : ℤ) :
    Subsingleton (DerivedCategory.Ext Q E i) ↔
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj (derivedDual X.sheaf Q)).obj E))) := by
  let := derivedMonoidalStructure X.sheaf
  let := derivedSymmetricStructure X.sheaf
  have e : ((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf Q) ≅
      ((derivedTensor X.sheaf).obj (derivedDual X.sheaf Q)).obj E := by
    rw [← curriedTensor_derivedMonoidalStructure]
    exact β_ E (derivedDual X.sheaf Q)
  refine (subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect Q E hQ i).trans ?_
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
    ((derivedModuleGlobalSections (ringedSite X.sheaf)).mapIso e))

/-- `H^i(X, P ⊗^L E)` vanishes exactly when `Ext^i_X(P^∨, E)` does, for a perfect `P`. -/
theorem isZero_homology_tensor_iff_subsingleton_ext_dual
    (P E : DerivedCategory (StructureSheafModules X.sheaf))
    (hP : (ringedSite X.sheaf).IsPerfect P) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj P).obj E))) ↔
      Subsingleton (DerivedCategory.Ext (derivedDual X.sheaf P) E i) := by
  refine Iff.trans ?_ (subsingleton_ext_iff_isZero_homology_dual_tensor _ E
    (isPerfect_derivedDual X.sheaf P hP) i).symm
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
    ((derivedModuleGlobalSections (ringedSite X.sheaf)).mapIso
      (((derivedTensor X.sheaf).mapIso (derivedBidualIso X.sheaf P hP)).app E)))

end Clauses

/-! ### The propositions -/

section Propositions

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- For a perfect `Q` and a filter `l` on `ℤ`, the eventual vanishing along `l` of
`Hom(Q⟦-i⟧, E)`, of `Ext^i(Q, E)`, of `H^i(RHom_X(Q, E))` and of `H^i(X, Q^∨ ⊗^L E)` are
equivalent. -/
private theorem eventually_clauses_iff (Q E : DerivedCategory (StructureSheafModules X.sheaf))
    (hQ : (ringedSite X.sheaf).IsPerfect Q) (l : Filter ℤ) :
    ((∀ᶠ i in l, Subsingleton (Q⟦-i⟧ ⟶ E)) ↔ ∀ᶠ i in l, Subsingleton (DerivedCategory.Ext Q E i)) ∧
    ((∀ᶠ i in l, Subsingleton (DerivedCategory.Ext Q E i)) ↔
      ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
          (((globalDerivedHom X.sheaf).obj (op Q)).obj E)))) ∧
    ((∀ᶠ i in l, Subsingleton (DerivedCategory.Ext Q E i)) ↔
      ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj (derivedDual X.sheaf Q)).obj E)))) :=
  ⟨eventually_congr (Eventually.of_forall fun i ↦ subsingleton_shiftedHom_iff_ext Q E i),
    eventually_congr (Eventually.of_forall fun i ↦
      subsingleton_ext_iff_isZero_homology_globalDerivedHom Q E i),
    eventually_congr (Eventually.of_forall fun i ↦
      subsingleton_ext_iff_isZero_homology_dual_tensor Q E hQ i)⟩

/-- If `E` has eventually vanishing cohomology sheaves along `l` and perfect objects have
eventually vanishing `Hom(Q⟦-i⟧, E)`, then all the clauses hold along `l` for a perfect `P`. -/
private theorem eventually_clauses_of_perfect
    (P E : DerivedCategory (StructureSheafModules X.sheaf))
    (hP : (ringedSite X.sheaf).IsPerfect P) (l : Filter ℤ)
    (h12 : ∀ Q, (ringedSite X.sheaf).IsPerfect Q →
      (∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor
        (StructureSheafModules X.sheaf) i).obj E)) → ∀ᶠ i in l, Subsingleton (Q⟦-i⟧ ⟶ E))
    (h1 : ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E)) :
    ((∀ᶠ i in l, Subsingleton (P⟦-i⟧ ⟶ E)) ∧
      (∀ᶠ i in l, Subsingleton (DerivedCategory.Ext P E i)) ∧
      ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
          (((globalDerivedHom X.sheaf).obj (op P)).obj E)))) ∧
    (∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj P).obj E)))) ∧
    ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj P).obj E))) := by
  obtain ⟨c23, c34, -⟩ := eventually_clauses_iff P E hP l
  have h2 := h12 P hP h1
  have hb : ∀ᶠ i in l, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
        (((derivedTensor X.sheaf).obj P).obj E))) :=
    ((eventually_clauses_iff _ E (isPerfect_derivedDual X.sheaf P hP) l).1.1
      (h12 _ (isPerfect_derivedDual X.sheaf P hP) h1)).mono
      fun i hi ↦ (isZero_homology_tensor_iff_subsingleton_ext_dual P E hP i).2 hi
  exact ⟨⟨h2, c23.1 h2, c34.1 (c23.1 h2)⟩, hb, hb⟩

/-- Let `X` be a quasi-compact and quasi-separated scheme, let `G` be a perfect
object of `D(𝒪_X)` which generates `D_QCoh(𝒪_X)`, and let `E ∈ D_QCoh(𝒪_X)`. The following are
equivalent:

1. `E ∈ D^-_QCoh(𝒪_X)`;
2. `Hom_{D(𝒪_X)}(G[-i], E) = 0` for `i ≫ 0`;
3. `Ext^i_X(G, E) = 0` for `i ≫ 0`;
4. `RHom_X(G, E)` is in `D^-(ℤ)`;
5. `H^i(X, G^∨ ⊗^L E) = 0` for `i ≫ 0`;
6. `RΓ(X, G^∨ ⊗^L E)` is in `D^-(ℤ)`;
7. for every perfect object `P` of `D(𝒪_X)`: (a) the assertions (2), (3), (4) hold with `G`
   replaced by `P`, (b) `H^i(X, P ⊗^L E) = 0` for `i ≫ 0`, and (c) `RΓ(X, P ⊗^L E)` is in
   `D^-(ℤ)`.

Generation of `D_QCoh(𝒪_X)` by `G` is the hypothesis that an object of `D(𝒪_X)` with
quasi-coherent cohomology receiving only zero morphisms from the shifts of `G` is zero, and
`E ∈ D_QCoh(𝒪_X)` is quasi-coherence of the cohomology sheaves of `E`. `RHom_X(G, E)` is the
global derived hom, read in `D(ℤ)`; `D^-(ℤ)` is the property `minus` of the canonical
t-structure on `D(AddCommGrpCat)`. -/
@[stacks 0GEN]
theorem tfae_minus_of_isPerfect_generator
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    List.TFAE
      [(DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).minus E,
        ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (G⟦-i⟧ ⟶ E),
        ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext G E i),
        (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).minus
          ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
            (((globalDerivedHom X.sheaf).obj (op G)).obj E)),
        ∃ N : ℤ, ∀ i, N ≤ i → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
          ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
            (((derivedTensor X.sheaf).obj (derivedDual X.sheaf G)).obj E))),
        (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).minus
          ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
            (((derivedTensor X.sheaf).obj (derivedDual X.sheaf G)).obj E)),
        ∀ P : DerivedCategory (StructureSheafModules X.sheaf), (ringedSite X.sheaf).IsPerfect P →
          ((∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E)) ∧
            (∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext P E i)) ∧
            (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).minus
              ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
                (((globalDerivedHom X.sheaf).obj (op P)).obj E))) ∧
          (∃ N : ℤ, ∀ i, N ≤ i → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
            ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj P).obj E)))) ∧
          (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).minus
            ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj P).obj E))] := by
  simp only [DerivedCategory.minus_iff, ← eventually_atTop]
  have h12 : ∀ P, (ringedSite X.sheaf).IsPerfect P →
      (∀ᶠ i in atTop, IsZero ((DerivedCategory.homologyFunctor
        (StructureSheafModules X.sheaf) i).obj E)) →
      ∀ᶠ i in atTop, Subsingleton (P⟦-i⟧ ⟶ E) := fun P hP h1 ↦
    eventually_atTop.2 (eventually_subsingleton_shiftedHom_of_minus hqc hqs P E hP hE
      ((DerivedCategory.minus_iff E).2 (eventually_atTop.1 h1)))
  obtain ⟨b23, b34, b35⟩ := eventually_clauses_iff G E hG atTop
  tfae_have 1 → 2 := h12 G hG
  tfae_have 2 → 1 := fun h ↦ (minus_iff_bdd E).1 (minus_of_eventually_subsingleton_shiftedHom
    hqc hqs G E hG hgen hE (eventually_atTop.1 h))
  tfae_have 2 ↔ 3 := b23
  tfae_have 3 ↔ 4 := b34
  tfae_have 3 ↔ 5 := b35
  tfae_have 5 ↔ 6 := Iff.rfl
  tfae_have 1 → 7 := fun h1 P hP ↦ eventually_clauses_of_perfect P E hP atTop h12 h1
  tfae_have 7 → 2 := fun h7 ↦ (h7 G hG).1.1
  tfae_finish

/-- Let `X` be a quasi-compact and quasi-separated scheme, let `G` be a perfect
object of `D(𝒪_X)` which generates `D_QCoh(𝒪_X)`, and let `E ∈ D_QCoh(𝒪_X)`. The following are
equivalent:

1. `E ∈ D^+_QCoh(𝒪_X)`;
2. `Hom_{D(𝒪_X)}(G[-i], E) = 0` for `i ≪ 0`;
3. `Ext^i_X(G, E) = 0` for `i ≪ 0`;
4. `RHom_X(G, E)` is in `D^+(ℤ)`;
5. `H^i(X, G^∨ ⊗^L E) = 0` for `i ≪ 0`;
6. `RΓ(X, G^∨ ⊗^L E)` is in `D^+(ℤ)`;
7. for every perfect object `P` of `D(𝒪_X)`: (a) the assertions (2), (3), (4) hold with `G`
   replaced by `P`, (b) `H^i(X, P ⊗^L E) = 0` for `i ≪ 0`, and (c) `RΓ(X, P ⊗^L E)` is in
   `D^+(ℤ)`.

Generation of `D_QCoh(𝒪_X)` by `G` is the hypothesis that an object of `D(𝒪_X)` with
quasi-coherent cohomology receiving only zero morphisms from the shifts of `G` is zero, and
`E ∈ D_QCoh(𝒪_X)` is quasi-coherence of the cohomology sheaves of `E`. `RHom_X(G, E)` is the
global derived hom, read in `D(ℤ)`; `D^+(ℤ)` is the property `plus` of the canonical
t-structure on `D(AddCommGrpCat)`. -/
@[stacks 0GEQ]
theorem tfae_plus_of_isPerfect_generator
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    List.TFAE
      [(DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).plus E,
        ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ E),
        ∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G E i),
        (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).plus
          ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
            (((globalDerivedHom X.sheaf).obj (op G)).obj E)),
        ∃ N : ℤ, ∀ i ≤ N, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
          ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
            (((derivedTensor X.sheaf).obj (derivedDual X.sheaf G)).obj E))),
        (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).plus
          ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
            (((derivedTensor X.sheaf).obj (derivedDual X.sheaf G)).obj E)),
        ∀ P : DerivedCategory (StructureSheafModules X.sheaf), (ringedSite X.sheaf).IsPerfect P →
          ((∃ N : ℤ, ∀ i ≤ N, Subsingleton (P⟦-i⟧ ⟶ E)) ∧
            (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext P E i)) ∧
            (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).plus
              ((RingedSite.underlyingDerivedGroup (ringedSite X.sheaf)).obj
                (((globalDerivedHom X.sheaf).obj (op P)).obj E))) ∧
          (∃ N : ℤ, ∀ i ≤ N, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
            ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj P).obj E)))) ∧
          (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).plus
            ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj P).obj E))] := by
  simp only [DerivedCategory.plus_iff, ← eventually_atBot]
  have h12 : ∀ P, (ringedSite X.sheaf).IsPerfect P →
      (∀ᶠ i in atBot, IsZero ((DerivedCategory.homologyFunctor
        (StructureSheafModules X.sheaf) i).obj E)) →
      ∀ᶠ i in atBot, Subsingleton (P⟦-i⟧ ⟶ E) := fun P hP h1 ↦
    eventually_atBot.2 (eventually_subsingleton_shiftedHom_of_plus' hqc hqs P E hP hE
      ((DerivedCategory.plus_iff E).2 (eventually_atBot.1 h1)))
  obtain ⟨b23, b34, b35⟩ := eventually_clauses_iff G E hG atBot
  tfae_have 1 → 2 := h12 G hG
  tfae_have 2 → 1 := fun h ↦ (plus_iff_bdd E).1 (plus_of_eventually_subsingleton_shiftedHom
    hqc hqs G E hG hgen hE (eventually_atBot.1 h))
  tfae_have 2 ↔ 3 := b23
  tfae_have 3 ↔ 4 := b34
  tfae_have 3 ↔ 5 := b35
  tfae_have 5 ↔ 6 := Iff.rfl
  tfae_have 1 → 7 := fun h1 P hP ↦ eventually_clauses_of_perfect P E hP atBot h12 h1
  tfae_have 7 → 2 := fun h7 ↦ (h7 G hG).1.1
  tfae_finish

end Propositions

end Stacks.SheafOfModules

end
