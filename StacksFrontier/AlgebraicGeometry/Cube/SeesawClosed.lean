module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction

/-!
# The locus where an invertible module is trivial on the fibres is closed

Let `k` be a field, `π : P ⟶ Spec k` a proper and geometrically integral morphism, `R` a
Noetherian `k`-algebra and `L` an invertible module on `P_R = P ×_k Spec R`. This file proves
that the set of primes `𝔭` of `R` such that `L` restricts to a trivial module on the fibre
`P_R ×_{Spec R} Spec κ(𝔭)` is closed in `Spec R`. This is the closedness half of the seesaw
principle, [Stacks, Tag 0BF0], and of Mumford, *Abelian varieties*, §5, Corollary 6; it is an
input of the theorem of the cube.

## Main results

* `AlgebraicGeometry.Cube.isClosed_setOf_isTrivial_fiber`: the seesaw locus is closed.
* `AlgebraicGeometry.Cube.nonempty_iso_unit_iff_nontrivial_sections`: on an integral scheme
  universally closed over a field, an invertible module is trivial if and only if it and its
  inverse both have nonzero global sections.
* `AlgebraicGeometry.Cube.isClosed_setOf_nontrivial_sections_fiber`: for `f : X ⟶ Spec A`
  proper with `A` Noetherian and `F` coherent and flat over `A`, the primes `𝔭` such that
  `F` has a nonzero global section on the fibre over `𝔭` form a closed set.
* `AlgebraicGeometry.Cube.nonempty_pullback_tensorPowerModule_neg_one_iso`: pulling back
  commutes with taking the inverse of an invertible module.

## Implementation notes

The fibres `P_{κ(𝔭)}` are integral and proper over `κ(𝔭)`, because `π` is geometrically
integral and proper, so their rings of global functions are fields. Hence `L_𝔭` is trivial
exactly when `L_𝔭` and `L_𝔭^{⊗ -1} = (L^{⊗ -1})_𝔭` have nonzero global sections, and each of
these two conditions is closed by upper semicontinuity of `𝔭 ↦ dim_{κ(𝔭)} H⁰(P_{κ(𝔭)}, -)`.
The semicontinuity is read off the Čech model of `RΓ(P_R, L)` on a finite affine cover: the
model is a perfect complex of `R`-modules
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isPerfect_Q_baseAlternatingCechComplex`),
its derived fibre at `𝔭` is the Čech model of the fibre, since the model is termwise flat, and the
fibre dimensions of a perfect complex are upper semicontinuous
(`StacksDraft.Perfect.upperSemicontinuous_finrank_homology_totalDerived`). The degree-zero
homology of a Čech model is the module of global sections
(`Stacks.Cech.range_sectionsToAlternatingₗ`), and it is finite-dimensional, so it is nonzero
exactly when its dimension is at least one.

## References

* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* D. Mumford, *Abelian varieties*, §5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible (tensorPowerModule mulNegOneIso)
open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isCoherent)

universe u

namespace AlgebraicGeometry.Cube

section Pointwise

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- The pullback of an invertible module is invertible, in the spelling of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_pullback :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pullback p).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry p.toLRSHom.toShHom L hL

/-- Tensoring with an invertible module reflects isomorphisms of objects, since it is an
equivalence. -/
private theorem nonempty_iso_of_tensor_iso {X : Scheme.{u}} (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    {A B : X.Modules}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj M).obj A ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj M).obj B) :
    Nonempty (A ≅ B) := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp
    _ X.presheaf (forget₂ CommRingCat RingCat) X.ringCatSheaf.property⟩).obj M
  have : F.IsEquivalence :=
    AlgebraicGeometry.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf
      X.ringCatSheaf.property M
  exact ⟨F.preimageIso e⟩

/-- **The pullback of the inverse of `L` is the inverse of the pullback of `L`.** Both are
tensor inverses of `p^* L` (`Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso` and
`Stacks.SheafOfModules.Invertible.mulNegOneIso`), and tensoring with the invertible module
`p^* L` is an equivalence, so it reflects isomorphisms of objects. -/
theorem nonempty_pullback_tensorPowerModule_neg_one_iso :
    haveI := isInvertible_pullback p L
    Nonempty ((Scheme.Modules.pullback p).obj (tensorPowerModule L (-1)) ≅
      tensorPowerModule ((Scheme.Modules.pullback p).obj L) (-1)) := by
  have := isInvertible_pullback p L
  let M := (Scheme.Modules.pullback p).obj L
  exact nonempty_iso_of_tensor_iso M
    (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackMulNegOneIso p L ≪≫
      (mulNegOneIso Y.presheaf Y.ringCatSheaf.property M).symm)

/-- Isomorphic sheaves of modules have isomorphic modules of global sections, so one of them has
nonzero global sections exactly when the other does. -/
theorem nontrivial_sections_iff_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Nontrivial Γ(M, ⊤) ↔ Nontrivial Γ(N, ⊤) := by
  let E : Γ(M, ⊤) ≃ Γ(N, ⊤) :=
    { toFun := fun x => PresheafOfModules.Hom.app e.hom.val (op ⊤) x
      invFun := fun y => PresheafOfModules.Hom.app e.inv.val (op ⊤) y
      left_inv := fun x => Stacks.SheafOfModules.isoValApp_inv_hom e (op ⊤) x
      right_inv := fun y => Stacks.SheafOfModules.isoValApp_hom_inv e (op ⊤) y }
  exact ⟨fun _ => E.symm.nontrivial, fun _ => E.nontrivial⟩

/-- **An invertible module on an integral scheme universally closed over a field is trivial
exactly when it and its inverse both have nonzero global sections.** One direction is
[Stacks, Tag 0B40] part (3): the ring of global functions is a field, so a nonzero product of two
global sections is a unit and trivializes the module. Conversely the structure sheaf has the
nonzero global section `1`, and the inverse of a trivial module is trivial. -/
theorem nonempty_iso_unit_iff_nontrivial_sections {κ : Type u} [Field κ] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of κ)) [IsIntegral X] [UniversallyClosed f] (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) ↔
      Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(tensorPowerModule L (-1), ⊤) := by
  have hO : Nontrivial Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) :=
    (isField_of_universallyClosed κ f).nontrivial
  constructor
  · rintro ⟨e⟩
    refine ⟨(nontrivial_sections_iff_of_iso e).2 hO, ?_⟩
    obtain ⟨e'⟩ := nonempty_iso_of_tensor_iso L (A := tensorPowerModule L (-1))
      (B := SheafOfModules.unit X.ringCatSheaf)
      (mulNegOneIso X.presheaf X.ringCatSheaf.property L ≪≫ e.symm ≪≫
        (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
          X.ringCatSheaf.property L).symm)
    exact (nontrivial_sections_iff_of_iso e').2 hO
  · rintro ⟨hs, ht⟩
    obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
    obtain ⟨t, ht⟩ := exists_ne (0 : Γ(tensorPowerModule L (-1), ⊤))
    exact isTrivial_of_eval_top_ne_zero_of_inverse κ f L
      (Stacks.PresheafOfModules.sectionOfTop L.val s)
      (fun h => hs ((Stacks.PresheafOfModules.sectionOfTop_val_top L.val s).symm.trans h))
      (Stacks.PresheafOfModules.sectionOfTop (tensorPowerModule L (-1)).val t)
      (fun h => ht ((Stacks.PresheafOfModules.sectionOfTop_val_top
        (tensorPowerModule L (-1)).val t).symm.trans h))

end Pointwise

section Model

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **The degree-zero homology of the Čech model is the module of global sections**, up to a
bijection: the alternating `0`-cocycles of a cover are the global sections
(`Stacks.Cech.range_sectionsToAlternatingₗ`). So the one is nonzero exactly when the other is. -/
theorem nontrivial_homology_zero_iff :
    Nontrivial ((baseAlternatingCechComplex f U hU F).homology ((0 : ℕ) : ℤ)) ↔
      Nontrivial Γ(F, ⊤) := by
  let := sectionsModule f F ⊤
  let := cochainModule f U F 0
  let := cochainModule f U F 1
  let Lc := alternatingCechModuleComplex f U F
  let eH : (baseAlternatingCechComplex f U hU F).homology ((0 : ℕ) : ℤ) ≅ Lc.homology 0 :=
    (HomologicalComplex.homologyFunctor _ _ ((0 : ℕ) : ℤ)).mapIso
        (baseAlternatingCechComplexIsoExtend f U hU F) ≪≫
      HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
        (j := 0) (j' := ((0 : ℕ) : ℤ)) rfl
  have hd0 : (Lc.d 0 1).hom = alternatingCechModuleD f U F 0 := by
    rw [alternatingCechModuleComplex_d f U F 0]
    rfl
  have hUW : ∀ i, U i ≤ (⊤ : X.Opens) := fun _ => le_top
  have hrange := range_sectionsToAlternatingₗ f U F hUW hU.le
  rw [← hd0] at hrange
  let e₁ : Γ(F, ⊤) ≃ₗ[A] LinearMap.range (sectionsToAlternatingₗ f U F hUW) :=
    LinearEquiv.ofInjective _ (sectionsToAlternatingₗ_injective f U F hUW hU.le)
  let e₂ : Γ(F, ⊤) ≃ₗ[A] Lc.homology 0 :=
    (e₁.trans (LinearEquiv.ofEq _ _ hrange)).trans (kerEquivHomologyZero Lc)
  let e := e₂.toEquiv.trans eH.toLinearEquiv.toEquiv.symm
  exact ⟨fun _ => e.nontrivial, fun _ => e.symm.nontrivial⟩

end Model

section Semicontinuity

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **The locus where the fibres of a flat coherent module have nonzero global sections is
closed.** Let `A` be Noetherian, `f : X ⟶ Spec A` proper and `F` a coherent `𝒪_X`-module flat
over `A`. Then the set of primes `𝔭` of `A` such that the pullback of `F` to the fibre
`X ×_{Spec A} Spec κ(𝔭)` has a nonzero global section is closed in `Spec A`.

This is upper semicontinuity of `𝔭 ↦ dim_{κ(𝔭)} H⁰(X_𝔭, F_𝔭)`: the Čech model of `RΓ(X, F)` on a
finite affine cover is perfect ([Stacks, Tag 07VK]), its derived fibre at `𝔭` is the Čech model
of the fibre, because the model is termwise flat, and the fibre dimensions of a perfect complex
are upper semicontinuous ([Stacks, Tag 0BDI]). -/
theorem isClosed_setOf_nontrivial_sections_fiber (F : X.Modules) [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsClosed {𝔭 : PrimeSpectrum A | Nontrivial Γ((Scheme.Modules.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔭.asIdeal.ResidueField))))).obj F, ⊤)} := by
  have := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  obtain ⟨I, hI, hlo, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  let K := DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F)
  have hsc := StacksDraft.Perfect.upperSemicontinuous_finrank_homology_totalDerived.{u, u} K
    (isPerfect_Q_baseAlternatingCechComplex f U hU F hUaff haff hflat) 0
  have hopen := upperSemicontinuous_iff_isOpen_preimage.1 hsc 1
  convert hopen.isClosed_compl using 1
  ext 𝔭
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]
  let κ := 𝔭.asIdeal.ResidueField
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A κ))
  have hsq : IsPullback (pullback.fst f φ) (pullback.snd f φ) f φ := IsPullback.of_hasPullback f φ
  have : IsLocallyNoetherian (pullback f φ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f φ)
  let F' := (Scheme.Modules.pullback (pullback.fst f φ)).obj F
  have : F'.IsCoherent := isCoherent_pullback (pullback.fst f φ) F
  have : F'.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent F').1
  let U' : I → (pullback f φ).Opens := fun i => pullback.fst f φ ⁻¹ᵁ U i
  have hU' : (⊤ : (pullback f φ).Opens) = ⨆ i, U' i := top_eq_iSup_preimage _ U hU
  have haff' := iInf_preimage_isAffineOpen (algebraMap A κ) hsq U hUaff
  let e := (DerivedCategory.homologyFunctor _ 0).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F (algebraMap A κ) hUaff hflat) ≪≫
    (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (baseAlternatingCechComplexBaseChangeIso (algebraMap A κ) hsq F U hU hUaff)
  have hfin : Module.Finite κ ((baseAlternatingCechComplex (pullback.snd f φ) U' hU' F').homology
      ((0 : ℕ) : ℤ)) :=
    moduleFinite_homology_baseAlternatingCechComplex (pullback.snd f φ) U' hU' F' haff'
      AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase.{u} 0
  have hfr : Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 0).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj K)) =
      Module.finrank κ ((baseAlternatingCechComplex (pullback.snd f φ) U' hU' F').homology
        ((0 : ℕ) : ℤ)) :=
    e.toLinearEquiv.finrank_eq
  rw [hfr, ← nontrivial_homology_zero_iff (pullback.snd f φ) U' hU' F']
  exact Module.finrank_pos_iff.symm

end Semicontinuity

section Seesaw

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f] [Flat f]

/-- An invertible module on a scheme flat over `A` is coherent and flat over `A`, so its fibre
sections have a closed nonvanishing locus. -/
theorem isClosed_setOf_nontrivial_sections_fiber_of_isInvertible (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    IsClosed {𝔭 : PrimeSpectrum A | Nontrivial Γ((Scheme.Modules.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔭.asIdeal.ResidueField))))).obj L, ⊤)} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have : L.IsQuasicoherent := (isQuasicoherent_isFiniteType_of_isCoherent L).1
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact isClosed_setOf_nontrivial_sections_fiber f L
    (AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f L)

/-- **The seesaw locus is closed.** Let `k` be a field, `π : P ⟶ Spec k` proper and geometrically
integral, `R` a Noetherian `k`-algebra and `L` an invertible module on `P_R = P ×_k Spec R`.
Then the set of primes `𝔭` of `R` such that the restriction of `L` to the fibre
`P_R ×_{Spec R} Spec κ(𝔭)` is trivial is closed in `Spec R`.

This is the closedness statement in the seesaw principle, [Stacks, Tag 0BF0] and Mumford,
*Abelian varieties*, §5. Each fibre is integral and proper over `κ(𝔭)`, so the restriction
`L_𝔭` is trivial exactly when `L_𝔭` and its inverse both have nonzero global sections
(`nonempty_iso_unit_iff_nontrivial_sections`), and each of these two conditions cuts out a
closed set by upper semicontinuity of `𝔭 ↦ h⁰(L_𝔭)`
(`isClosed_setOf_nontrivial_sections_fiber`). -/
theorem isClosed_setOf_isTrivial_fiber {k : Type u} [Field k] {P : Scheme.{u}}
    (π : P ⟶ Spec (.of k)) [IsProper π] [GeometricallyIntegral π]
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (L : (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatIsSheaf L) :
    IsClosed {𝔭 : PrimeSpectrum R | Nonempty ((Scheme.Modules.pullback (pullback.fst
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj L ≅
      SheafOfModules.unit _)} := by
  set f := pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).sheaf.obj
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property L := hL'
  have : Stacks.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property L := hL
  have : Stacks.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).sheaf.obj
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property L := hL
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property
      (tensorPowerModule L (-1)) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).presheaf
      (pullback π (Spec.map (CommRingCat.ofHom (algebraMap k R)))).ringCatSheaf.property L (-1)
  convert (isClosed_setOf_nontrivial_sections_fiber_of_isInvertible f L).inter
    (isClosed_setOf_nontrivial_sections_fiber_of_isInvertible f (tensorPowerModule L (-1)))
    using 1
  ext 𝔭
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  let φ := Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))
  have := isInvertible_pullback (pullback.fst f φ) L
  obtain ⟨e⟩ := nonempty_pullback_tensorPowerModule_neg_one_iso (pullback.fst f φ) L
  rw [nonempty_iso_unit_iff_nontrivial_sections (pullback.snd f φ),
    nontrivial_sections_iff_of_iso e]

end Seesaw

end AlgebraicGeometry.Cube

end
