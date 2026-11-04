module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.Devissage
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectBoundedCoherentTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentKGroupModule
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The product `K₀(X) × K'₀(X) ⟶ K'₀(X)` on a locally Noetherian scheme

Let `X` be a locally Noetherian scheme. For a perfect object `P` of `D(𝒪_X)` and an object `N`
with locally bounded coherent cohomology, `P ⊗^𝐋 N` again has locally bounded coherent
cohomology: over an affine open the restriction of `N` is bounded, the restriction of `P` is
perfect, and the derived tensor product of a perfect object with an object of `D^b_Coh` on a
Noetherian scheme lies in `D^b_Coh`. Hence

  `[P] · [ℱ] = χ(P ⊗^𝐋 ℱ) = [⨁_i H^{2i}(P ⊗^𝐋 ℱ)] − [⨁_i H^{2i+1}(P ⊗^𝐋 ℱ)]`

is a well defined bilinear map `K₀(X) × K'₀(X) ⟶ K'₀(X)`; this is the product of
[Stacks, Tag 0FDK]. On a Noetherian scheme the sums are finite and `χ(P ⊗^𝐋 ℱ)` is the class of
`P ⊗^𝐋 ℱ` in `K₀(D^b_Coh(𝒪_X)) = K'₀(X)`.

## Main definitions

* `AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul`: the bilinear map
  `K₀(X) ⟶ K'₀(X) ⟶ K'₀(X)`.

## Main results

* `AlgebraicGeometry.ParityEulerClass.isLocallyBoundedCoherent_of_local`: locally bounded
  coherent cohomology is local.
* `AlgebraicGeometry.ParityEulerClass.IsLocallyBoundedCoherent.derivedTensor`: the closure under
  tensoring with a perfect object.
* `AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul_cls_mk`: the value on classes.

## References

* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology

universe u

namespace AlgebraicGeometry.ParityEulerClass

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

variable {X : Scheme.{u}}

/-! ### Locality -/

/-- **Locally bounded coherent cohomology is a local property.** If every point has an open
neighbourhood on which the cohomology sheaves of `K` are those of an object of `D^b_Coh`, then
`K` has locally bounded coherent cohomology. -/
theorem isLocallyBoundedCoherent_of_local (K : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∃ L : DerivedCategory W.toScheme.Modules,
      DerivedCategoryB.derivedCategoryBBounded (fun F : W.toScheme.Modules => F.IsCoherent) L ∧
        ∀ q : ℤ, Nonempty ((Scheme.Modules.restrictFunctor W.ι).obj
          ((DerivedCategory.homologyFunctor X.Modules q).obj K) ≅
            (DerivedCategory.homologyFunctor W.toScheme.Modules q).obj L)) :
    IsLocallyBoundedCoherent K := by
  choose W hxW L hL e using h
  refine ⟨fun q => Modules.isCoherent_of_restrict _ W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) fun x =>
      ObjectProperty.prop_of_iso (P := SheafOfModules.IsCoherent) (e x q).some.symm
        ((hL x).2 q), fun x => ?_⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (hL x).1
  refine ⟨W x, (W x).isOpen.mem_nhds (hxW x), (Set.finite_Icc a b).subset fun q hq => ?_⟩
  by_contra hnot
  simp only [Set.mem_Icc, not_and_or, not_le] at hnot
  have hz : IsZero ((Scheme.Modules.restrictFunctor (W x).ι).obj
      ((DerivedCategory.homologyFunctor X.Modules q).obj K)) :=
    IsZero.of_iso (hnot.elim (ha q) (hb q)) (e x q).some
  obtain ⟨y, hy, hyW⟩ := hq
  exact Set.disjoint_left.1 (disjoint_of_isZero_restrict _ _ hz) hy hyW

/-- The cohomology sheaves of the restriction to an open are the restrictions of the cohomology
sheaves. -/
def restrictHomologyIso (W : X.Opens) (K : DerivedCategory X.Modules) (q : ℤ) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((DerivedCategory.homologyFunctor X.Modules q).obj K) ≅
      (DerivedCategory.homologyFunctor W.toScheme.Modules q).obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj K) :=
  (((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategoryHomologyIso q).app K).symm

/-- **Restriction to an open commutes with the derived tensor product.** Restriction to `W` is the
derived pullback along `W.ι`, which commutes with the derived tensor product by [Stacks, Tag
079U]. -/
def restrictDerivedTensorIso (W : X.Opens) (A B : DerivedCategory X.Modules) :
    (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj
        (((TorFormula.derivedTensor X).obj A).obj B) ≅
      ((TorFormula.derivedTensor W.toScheme).obj
          ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj A)).obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj B) :=
  let e := (Scheme.Modules.derivedRestrictModulesIsoDerivedPullback X W).symm ≪≫
    RingedSpace.derivedRestrictModulesIsoRestrictFunctor X W
  (e.app _).symm ≪≫
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      W.ι.toLRSHom.toShHom).app (A, B) ≪≫
    ((TorFormula.derivedTensor W.toScheme).mapIso (e.app A)).app _ ≪≫
    ((TorFormula.derivedTensor W.toScheme).obj _).mapIso (e.app B)

/-! ### Tensoring with a perfect object -/

/-- **Tensoring with a perfect object preserves locally bounded coherent cohomology.** Over an
affine open `W` on which `N` is bounded, the restriction of `P ⊗^𝐋 N` is the derived tensor
product of the perfect object `P|_W` with the object `N|_W` of `D^b_Coh(𝒪_W)`, and `W` is
Noetherian. -/
theorem IsLocallyBoundedCoherent.derivedTensor [IsLocallyNoetherian X]
    {P N : DerivedCategory X.Modules}
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (hN : IsLocallyBoundedCoherent N) :
    IsLocallyBoundedCoherent (((TorFormula.derivedTensor X).obj P).obj N) := by
  refine isLocallyBoundedCoherent_of_local _ fun x => ?_
  obtain ⟨s, hs, hfin⟩ := hN.2 x
  obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hs
  obtain ⟨_, ⟨W₀, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV hVo
  let W : X.Opens := W₀
  have : IsAffine W.toScheme := hW
  have : IsNoetherian W.toScheme := IsNoetherian.mk
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨b, hb⟩ := hfin.bddAbove
  have hz : ∀ q : ℤ, (q < a ∨ b < q) → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj N)) := by
    intro q hq
    refine IsZero.of_iso (isZero_restrict_of_disjoint _ W (Set.disjoint_left.2 fun y hy hyW => ?_))
      (restrictHomologyIso W N q).symm
    have hmem : q ∈ {q | (SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules q).obj N)
        ∩ s).Nonempty} := ⟨y, hy, hVs (hWV hyW)⟩
    exact hq.elim (not_le.2 · (ha hmem)) (not_le.2 · (hb hmem))
  have hRN : DerivedCategoryB.derivedCategoryBBounded (fun F : W.toScheme.Modules => F.IsCoherent)
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj N) :=
    ⟨⟨⟨a, fun q hq => hz q (Or.inl hq)⟩, ⟨b, fun q hq => hz q (Or.inr hq)⟩⟩, fun q =>
      ObjectProperty.prop_of_iso (P := SheafOfModules.IsCoherent)
        (restrictHomologyIso W N q) (Modules.isCoherent_restrict (hM := hN.1 q) _ _)⟩
  exact ⟨W, hxW, _, derivedCategoryBBounded_derivedTensor_of_isPerfect W.toScheme _ _
    (Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory X W P hP) hRN, fun q =>
      ⟨restrictHomologyIso W _ q ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (restrictDerivedTensorIso W P N)⟩⟩

/-- The `𝒪_X`-module placed in degree `0`, tensored with a perfect object, has locally bounded
coherent cohomology. -/
theorem isLocallyBoundedCoherent_derivedTensor_single [IsLocallyNoetherian X]
    {P : DerivedCategory X.Modules}
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (F : X.Modules) (hF : F.IsCoherent) :
    IsLocallyBoundedCoherent (((TorFormula.derivedTensor X).obj P).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  IsLocallyBoundedCoherent.derivedTensor hP (isLocallyBoundedCoherent_single F hF)

/-- **`ℱ ↦ χ(P ⊗^𝐋 ℱ)` is additive along short exact sequences.** A short exact sequence placed in
degree `0` is a distinguished triangle, tensoring with `P` is exact, and `χ` is additive along
distinguished triangles. -/
theorem parityEulerClass_derivedTensor_shortExact [IsLocallyNoetherian X]
    {P : DerivedCategory X.Modules}
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (T : ShortComplex X.Modules) (hT : T.ShortExact) (h₁ : T.X₁.IsCoherent)
    (h₂ : T.X₂.IsCoherent) (h₃ : T.X₃.IsCoherent) :
    parityEulerClass (((TorFormula.derivedTensor X).obj P).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj T.X₂)) =
      parityEulerClass (((TorFormula.derivedTensor X).obj P).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj T.X₁)) +
        parityEulerClass (((TorFormula.derivedTensor X).obj P).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj T.X₃)) := by
  let : ((TorFormula.derivedTensor X).obj P).CommShift ℤ :=
    (derivedTensorStructureAtScheme X).commShiftRight P
  let : ((TorFormula.derivedTensor X).obj P).IsTriangulated :=
    (derivedTensorStructureAtScheme X).isTriangulatedRight P
  exact parityEulerClass_obj₂ _ (((TorFormula.derivedTensor X).obj P).map_distinguished _
    hT.singleTriangle_distinguished) (isLocallyBoundedCoherent_derivedTensor_single hP _ h₁)
    (isLocallyBoundedCoherent_derivedTensor_single hP _ h₂)
    (isLocallyBoundedCoherent_derivedTensor_single hP _ h₃)

/-! ### The product -/

variable (X) in
/-- For a perfect object `P`, the homomorphism `K'₀(X) ⟶ K'₀(X)`, `[ℱ] ↦ χ(P ⊗^𝐋 ℱ)`. -/
def perfectCoherentSMulAux [IsLocallyNoetherian X]
    (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X) :
    CoherentKZero X →+ CoherentKZero X :=
  KZero.lift (fun F => parityEulerClass (((TorFormula.derivedTensor X).obj P.obj).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj))) fun S hS =>
    let Pc : ObjectProperty (SheafOfModules.{u} X.ringCatSheaf) :=
      Stacks.SheafOfModules.coherentModules X.ringCatSheaf
    let : PreservesFiniteLimits Pc.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
    let : PreservesFiniteColimits Pc.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
    parityEulerClass_derivedTensor_shortExact P.property _ (hS.map_of_exact Pc.ι)
      (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₁.property)
      (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₂.property)
      (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₃.property)

/-- `perfectCoherentSMulAux X P` sends the class of a coherent module `ℱ` to `χ(P ⊗^𝐋 ℱ)`. -/
theorem perfectCoherentSMulAux_mk [IsLocallyNoetherian X]
    (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    perfectCoherentSMulAux X P (KZero.mk _ F) = parityEulerClass
      (((TorFormula.derivedTensor X).obj P.obj).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) :=
  KZero.lift_mk _ _ F

/-- **`P ↦ χ(P ⊗^𝐋 ℱ)` is additive along distinguished triangles of perfect objects.** -/
theorem perfectCoherentSMulAux_obj₂ [IsLocallyNoetherian X]
    (T : Triangle (Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X))
    (hT : T ∈ distTriang _) :
    perfectCoherentSMulAux X T.obj₂ =
      perfectCoherentSMulAux X T.obj₁ + perfectCoherentSMulAux X T.obj₃ := by
  refine KZero.hom_ext fun F => ?_
  rw [AddMonoidHom.add_apply, perfectCoherentSMulAux_mk, perfectCoherentSMulAux_mk,
    perfectCoherentSMulAux_mk]
  let L := (DerivedCategory.singleFunctor X.Modules 0).obj F.obj
  have hF : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  let : ((TorFormula.derivedTensor X).flip.obj L).CommShift ℤ :=
    (derivedTensorStructureAtScheme X).commShiftLeft L
  let : ((TorFormula.derivedTensor X).flip.obj L).IsTriangulated :=
    (derivedTensorStructureAtScheme X).isTriangulatedLeft L
  exact parityEulerClass_obj₂ _ (((TorFormula.derivedTensor X).flip.obj L).map_distinguished _
      ((ObjectProperty.ι _).map_distinguished T hT))
    (isLocallyBoundedCoherent_derivedTensor_single T.obj₁.property _ hF)
    (isLocallyBoundedCoherent_derivedTensor_single T.obj₂.property _ hF)
    (isLocallyBoundedCoherent_derivedTensor_single T.obj₃.property _ hF)

variable (X) in
/-- **The product `K₀(X) × K'₀(X) ⟶ K'₀(X)` of [Stacks, Tag 0FDK]**, for a locally Noetherian
scheme `X`: the class of a perfect object `P` times the class of a coherent module `ℱ` is the
parity Euler class `[⨁_i H^{2i}(P ⊗^𝐋 ℱ)] − [⨁_i H^{2i+1}(P ⊗^𝐋 ℱ)]` of `P ⊗^𝐋 ℱ`; on a
Noetherian scheme this is the class of `P ⊗^𝐋 ℱ` in `K₀(D^b_Coh(𝒪_X)) = K'₀(X)`. It is
bilinear, additivity in the first variable being encoded in the outer homomorphism. -/
def perfectCoherentSMul [IsLocallyNoetherian X] :
    PerfectKZero X →+ CoherentKZero X →+ CoherentKZero X :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift (perfectCoherentSMulAux X)) fun a ha => by
    refine (AddSubgroup.closure_le
      (K := (FreeAbelianGroup.lift (perfectCoherentSMulAux X)).ker)).2 ?_ ha
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, perfectCoherentSMulAux_obj₂ T hT]
    abel

/-- **The value of the product on classes**: `[P] · [ℱ] = χ(P ⊗^𝐋 ℱ)`. -/
theorem perfectCoherentSMul_cls_mk [IsLocallyNoetherian X]
    (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    perfectCoherentSMul X (Pretriangulated.K0.cls P) (KZero.mk _ F) = parityEulerClass
      (((TorFormula.derivedTensor X).obj P.obj).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) := by
  simp only [perfectCoherentSMul, Pretriangulated.K0.cls]
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  exact perfectCoherentSMulAux_mk P F

end AlgebraicGeometry.ParityEulerClass
