module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistedSections
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.ModuleFlatLocus
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.WeaklyAssociatedLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Functor
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Twist
public import StacksFrontier.AlgebraicGeometry.Quot.QuotValuativeAffineChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The valuative criterion for `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}`: existence

Let `R` be a valuation ring with fraction field `K`. This file proves that every `K`-point of the
scheme-level functor `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` of
`AlgebraicGeometry.ProjectiveQuot.hilbertFunctor` extends to an `R`-point: this is the existence
part of the valuative criterion of Stacks 03IX for `Quot^P ⟶ Spec ℤ`, which the proof of
Stacks 0DPA takes from Stacks 0DM4.

## The construction

The source takes the closure of the kernel chart by chart and glues. Here the closure is defined
globally: for `g : T' ⟶ T` with base change `j : ℙⁿ_{T'} ⟶ ℙⁿ_T` and `K ⊆ 𝒪^{⊕ r}` on `ℙⁿ_{T'}`,
`AlgebraicGeometry.ProjectiveQuot.closure g K` is the kernel of the adjoint
`𝒪^{⊕ r} ⟶ j_*(𝒪^{⊕ r} / K)` of the quotient map. This is the sheaf form of the generic kernel
of `StacksDraft.GenericFibre.existsUnique_submodule_flat_quotient` (the affine-chart case of
Stacks 0DM4, whose Stacks 0539 step `StacksDraft.GenericFibre.flat_of_isTorsionFree` is reused
below); being defined globally, it needs no gluing. Then:

* the closure **restricts back** to `K` whenever `j` is a flat affine monomorphism
  (`AlgebraicGeometry.ProjectiveQuot.baseChange_closure`): the counit `j^* j_* 𝒢 ⟶ 𝒢` is
  invertible along an affine monomorphism (affine base change, Stacks 02KG, at the kernel-pair
  square of `j`) and `j^*` is exact;
* for `g : Spec K ⟶ Spec R` the quotient is **torsion free**, hence **flat** over the valuation
  ring `R` (Stacks 0539 on every affine chart, then the affine-local criterion Stacks 01U4);
* it is of **finite presentation**: a flat quasi-coherent quotient of `𝒪^{⊕ r}` over a base with
  one weakly associated point (Stacks 05IK, where the source cites 0DLR);
* it has **Hilbert polynomial `P` on every fibre**: `s ↦ χ(ℙⁿ_{κ(s)}, ℱ_s(d))` is locally constant
  on the connected `Spec R` (Stacks 0B9T) and is `P(d)` at the generic point.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.exists_baseChange_eq_of_valuationRing`: **the existence part
  of the valuative criterion** for `Quot^P`.
* `AlgebraicGeometry.ProjectiveQuot.baseChange_closure`: the closure along a flat affine
  monomorphism of bases restricts back.
* `AlgebraicGeometry.ProjectiveQuot.isFlatOver_quotient_closure`,
  `AlgebraicGeometry.ProjectiveQuot.isFinitePresentation_quotient_closure`: the closure over a
  valuation ring is a flat family of finite presentation.
* `AlgebraicGeometry.ProjectiveQuot.hilbertPolynomial_fibre_eq_fibreEulerCharacteristic`: the
  Hilbert polynomial of a fibre of a flat family on `ℙⁿ_T` is read off the Euler characteristic
  function of Stacks 0B9T.
* `AlgebraicGeometry.isIso_pullbackPushforwardAdjunction_counit_app_of_mono`: the counit of
  `j^* ⊣ j_*` is invertible at quasi-coherent modules along an affine monomorphism.

## What is not proved here

The uniqueness half of the valuative criterion (separatedness) is not proved in this file. The
route through the closure would need the unit `𝒬 ⟶ j_* j^* 𝒬` to be a monomorphism for `𝒬`
flat over `R`, a computation of the sections of `j^* 𝒬` over affine opens.

No tag is registered: this is an input of Stacks 0DPA, and the tags 0DM4 and 03IX concern the
Quot functor of algebraic spaces.

## References

* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Along an affine monomorphism the counit `j^* j_* 𝒢 ⟶ 𝒢` is invertible** at every
quasi-coherent `𝒢`. A monomorphism `j` is its own kernel pair, so the square with two identities
and two copies of `j` is cartesian, and affine base change (Stacks 02KG) makes its base-change
morphism `j^* j_* 𝒢 ⟶ 𝟙_* 𝟙^* 𝒢` invertible. That morphism is `j^* j_*` of the unit of the
pullback along the identity, then `j^*` of an identification of direct images, then the counit
at `𝟙_* 𝟙^* 𝒢`; the first two are invertible, hence so is the counit at `𝟙_* 𝟙^* 𝒢`, and by
naturality along the invertible unit `𝒢 ⟶ 𝟙_* 𝟙^* 𝒢` so is the counit at `𝒢`. -/
theorem isIso_pullbackPushforwardAdjunction_counit_app_of_mono {X Y : Scheme.{u}} (j : X ⟶ Y)
    [Mono j] [IsAffineHom j] (G : X.Modules) [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app G) := by
  have hsq : IsPullback (𝟙 X) (𝟙 X) j j := IsKernelPair.id_of_mono j
  have hβ := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hsq G
  rw [Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeNatTrans_app_eq] at hβ
  have hη := Stacks.Veronese.isIso_modulesPullbackPushforwardUnit_app (𝟙 X) G
  have h₁ : IsIso ((Scheme.Modules.pullback j).map ((Scheme.Modules.pushforward j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app G))) := inferInstance
  have h₂ : IsIso ((Scheme.Modules.pullback j).map
      ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso hsq.w).hom.app
        ((Scheme.Modules.pullback (𝟙 X)).obj G))) := inferInstance
  rw [isIso_comp_left_iff, isIso_comp_left_iff] at hβ
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction j).counit.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app G)
  simp only [Functor.comp_map, Functor.id_map] at hnat
  dsimp only [Functor.id_obj, Functor.comp_obj] at hnat
  have h₄ : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app G ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app G) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app G)

/-- In an abelian category the morphism `X / ker f ⟶ Y` induced by `f` is a monomorphism. -/
theorem _root_.CategoryTheory.Abelian.mono_cokernel_desc_kernelSubobject_arrow {C : Type*}
    [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    Mono (cokernel.desc (kernelSubobject f).arrow f (kernelSubobject_arrow_comp f)) := by
  let e : cokernel (kernelSubobject f).arrow ≅ cokernel (kernel.ι f) :=
    cokernel.mapIso _ _ (kernelSubobjectIso f) (Iso.refl _) (by simp)
  have h : cokernel.desc (kernelSubobject f).arrow f (kernelSubobject_arrow_comp f) =
      e.hom ≫ Abelian.factorThruCoimage f := by
    refine coequalizer.hom_ext ?_
    simp [e, Abelian.factorThruCoimage]
  rw [h]
  infer_instance

namespace ProjectiveQuot

variable {n r : ℕ}

/-- The free module `𝒪^{⊕ r}` on `ℙⁿ_T` is of finite type. -/
theorem isFiniteType_freeModule (T : Scheme.{u}) : (freeModule n r T).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso
    (M := SheafOfModules.free (R := (projectiveSpaceOver n T).ringCatSheaf) (ULift.{u} (Fin r)))
    ((SheafOfModules.isColimitFreeCofan (R := (projectiveSpaceOver n T).ringCatSheaf)
        (ULift.{u} (Fin r))).coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
      Sigma.whiskerEquiv
        (f := fun _ : ULift.{u} (Fin r) =>
          SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf)
        (g := fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T))
        Equiv.ulift (fun _ => Iso.refl _))

/-! ### Fibrewise Euler characteristics -/

section Euler

open ProperFlatFibreEulerCharacteristic

/-- For a flat family and any cartesian square over a field-valued point `p : Spec k ⟶ T`, the
dimension of `H^j` of the base change is the `j`-th fibre Betti number at the image of `p`. -/
theorem finrank_cohomologyOverField_eq_fibreBetti {Y T : Scheme.{u}} {π : Y ⟶ T}
    {F : Y.Modules} (h : FibreBetti.IsFlatFamily π F) (k : Type u) [Field k]
    (p : Spec (.of k) ⟶ T) {Yk : Scheme.{u}} (πk : Yk ⟶ Spec (.of k)) (q : Yk ⟶ Y)
    (hsq : IsPullback q πk π p) (pt : Spec (.of k)) (j : ℕ) :
    Module.finrank k (cohomologyOverField k πk ((Scheme.Modules.pullback q).obj F) j) =
      FibreBetti.fibreBetti π F j (p.base pt) := by
  have hpb := congrFun (FibreBetti.fibreBetti_pullback hsq h (j : ℤ)) pt
  simp only [Function.comp_apply] at hpb
  rw [← hpb, FibreBetti.fibreBetti_eq_derivedFiberBetti (FibreBetti.isFlatFamily_pullback hsq h)]
  exact (DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule k πk
    ((Scheme.Modules.pullback q).obj F) _ j pt).symm

/-- **The Euler characteristic of any field-valued fibre** of a flat family is the value of
`s ↦ χ(X_s, ℱ_s)` (Stacks 0B9T) at the image point. -/
theorem eulerSum_eq_fibreEulerCharacteristic {Y T : Scheme.{u}} {π : Y ⟶ T}
    {F : Y.Modules} (h : FibreBetti.IsFlatFamily π F) (k : Type u) [Field k]
    (p : Spec (.of k) ⟶ T) {Yk : Scheme.{u}} (πk : Yk ⟶ Spec (.of k)) (q : Yk ⟶ Y)
    (hsq : IsPullback q πk π p) (pt : Spec (.of k)) :
    eulerSum k πk ((Scheme.Modules.pullback q).obj F) =
      fibreEulerCharacteristic π F (p.base pt) := by
  have key : ∀ (k : Type u) [Field k] (p : Spec (.of k) ⟶ T) {Yk : Scheme.{u}}
      (πk : Yk ⟶ Spec (.of k)) (q : Yk ⟶ Y) (_ : IsPullback q πk π p) (pt : Spec (.of k)),
      eulerSum k πk ((Scheme.Modules.pullback q).obj F) =
        ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (FibreBetti.fibreBetti π F j (p.base pt) : ℤ) := by
    intro k _ p Yk πk q hsq pt
    refine finsum_congr fun j => ?_
    rw [finrank_cohomologyOverField_eq_fibreBetti h k p πk q hsq pt j]
  have h₂ := key (T.residueField (p.base pt)) (T.fromSpecResidueField (p.base pt)) _ _
    (FibreBetti.isPullback_fiberι_fiberToSpecResidueField π (p.base pt))
    (IsLocalRing.closedPoint (CommRingCat.of ↑(T.residueField (p.base pt))))
  rw [Scheme.fromSpecResidueField_apply (p.base pt)
    (IsLocalRing.closedPoint (CommRingCat.of ↑(T.residueField (p.base pt))))] at h₂
  exact (key k p πk q hsq pt).trans h₂.symm

variable {n : ℕ}

/-- The hypotheses of the fibre Betti numbers for the twists of a flat family on `ℙⁿ_T`. -/
theorem isFlatFamily_twist {T : Scheme.{u}} {F : (projectiveSpaceOver n T).Modules}
    (hF : IsFlatFamily F) (d : ℤ) :
    FibreBetti.IsFlatFamily (projectiveSpaceOver n T ↘ T) (twist d F) :=
  ⟨finitePresentation_projectiveSpaceOver n T, inferInstance,
    isFinitePresentation_twist _ _ hF.1, isFlatOver_twist _ _ _ hF.2⟩

/-- **The Hilbert polynomial of a fibre of a flat family on `ℙⁿ_T`** at `d` is the Euler
characteristic `χ(ℙⁿ_{κ(t)}, ℱ_t(d))` of Stacks 0B9T for the twist `ℱ(d)`. -/
theorem hilbertPolynomial_fibre_eq_fibreEulerCharacteristic {T : Scheme.{u}}
    {F : (projectiveSpaceOver n T).Modules} (hF : IsFlatFamily F) (t : T)
    [(fibre t F).IsCoherent] (d : ℤ) :
    hilbertPolynomial (T.residueField t) n (fibre t F) d =
      fibreEulerCharacteristic (projectiveSpaceOver n T ↘ T) (twist d F) t := by
  have h := eulerSum_eq_fibreEulerCharacteristic (isFlatFamily_twist hF d) (T.residueField t)
    (T.fromSpecResidueField t) _ (fibreMap n t)
    (isPullback_projectiveSpaceOverMap n (T.fromSpecResidueField t))
    (IsLocalRing.closedPoint (CommRingCat.of ↑(T.residueField t)))
  rw [Scheme.fromSpecResidueField_apply t
    (IsLocalRing.closedPoint (CommRingCat.of ↑(T.residueField t)))] at h
  rw [← h, ← eulerSum_congr _ _ (twistPullbackIso (T.fromSpecResidueField t) d F)]
  rfl

end Euler

/-! ### The closure of a family along a morphism of bases -/

section Closure

variable {T' T : Scheme.{u}} (g : T' ⟶ T) (K : Subobject (freeModule n r T'))

/-- The morphism `𝒪^{⊕ r} ⟶ j_*(𝒪^{⊕ r} / K)` on `ℙⁿ_T` adjoint to the quotient map
`j^* 𝒪^{⊕ r} ≅ 𝒪^{⊕ r} ⟶ 𝒪^{⊕ r} / K` on `ℙⁿ_{T'}`, for `j : ℙⁿ_{T'} ⟶ ℙⁿ_T` the base change
of `g`. -/
def closureMap :
    freeModule n r T ⟶
      (Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).obj (quotient K) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOverMap n g)).homEquiv _ _
    ((freeModulePullbackIso n r g).hom ≫ quotientπ K)

/-- **The closure of `K` along `g`**: the kernel of `𝒪^{⊕ r} ⟶ j_*(𝒪^{⊕ r} / K)`. For `g` the
inclusion of the generic point of a valuation ring this is the closure of the kernel of
Stacks 0DM4. -/
def closure : Subobject (freeModule n r T) :=
  kernelSubobject (closureMap g K)

/-- The quotient by the closure embeds into `j_*(𝒪^{⊕ r} / K)`. -/
def closureQuotientι : quotient (closure g K) ⟶
    (Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).obj (quotient K) :=
  cokernel.desc _ (closureMap g K) (kernelSubobject_arrow_comp _)

/-- The map `𝒪^{⊕ r} / \bar K ⟶ j_*(𝒪^{⊕ r} / K)` is a monomorphism. -/
instance : Mono (closureQuotientι g K) :=
  Abelian.mono_cokernel_desc_kernelSubobject_arrow _

/-- The quotient map by the closure followed by `closureQuotientι g K` is `closureMap g K`. -/
@[reassoc (attr := simp)]
theorem quotientπ_closureQuotientι : quotientπ (closure g K) ≫ closureQuotientι g K =
    closureMap g K :=
  cokernel.π_desc _ _ _

/-- The morphism `j^*(𝒪^{⊕ r} / \bar K) ⟶ 𝒪^{⊕ r} / K` of the closure: the pullback of the
embedding into `j_*(𝒪^{⊕ r} / K)`, followed by the counit. -/
def closureComparison :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (quotient (closure g K)) ⟶
      quotient K :=
  (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (closureQuotientι g K) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOverMap n g)).counit.app _

/-- The base-changed quotient map by the closure followed by `closureComparison g K` is the
quotient map `𝒪^{⊕ r} ⟶ 𝒪^{⊕ r} / K`. -/
theorem baseChangeQuotientMap_closureComparison :
    baseChangeQuotientMap g (closure g K) ≫ closureComparison g K = quotientπ K := by
  rw [baseChangeQuotientMap, closureComparison, Category.assoc, ← Functor.map_comp_assoc,
    quotientπ_closureQuotientι, closureMap, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply,
    Iso.inv_hom_id_assoc]

/-- If `j` is affine and `𝒪^{⊕ r} / K` is quasi-coherent, then so is `𝒪^{⊕ r} / \bar K`. -/
instance isQuasicoherent_quotient_closure [IsAffineHom (projectiveSpaceOverMap n g)]
    [(quotient K).IsQuasicoherent] : (quotient (closure g K)).IsQuasicoherent := by
  have h1 : (freeModule n r T).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit _
      fun _ => Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have h3 : (closure g K : (projectiveSpaceOver n T).Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver n T).ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (closureMap g K)).symm
      ((SheafOfModules.isQuasicoherent (projectiveSpaceOver n T).ringCatSheaf).prop_kernel _ h1
        inferInstance)
  infer_instance

section Generic

variable [Flat (projectiveSpaceOverMap n g)] [Mono (projectiveSpaceOverMap n g)]
  [IsAffineHom (projectiveSpaceOverMap n g)] [(quotient K).IsQuasicoherent]

/-- Along a flat affine monomorphism `j`, the map `closureComparison g K` is a monomorphism. -/
instance : Mono (closureComparison g K) := by
  have := preservesFiniteLimits_modulesPullback_of_flat (projectiveSpaceOverMap n g)
  have := isIso_pullbackPushforwardAdjunction_counit_app_of_mono (projectiveSpaceOverMap n g)
    (quotient K)
  unfold closureComparison
  infer_instance

/-- The map `closureComparison g K` is an epimorphism. -/
instance : Epi (closureComparison g K) :=
  epi_of_epi_fac (baseChangeQuotientMap_closureComparison g K)

/-- Along a flat affine monomorphism `j`, the map `j^*(𝒪^{⊕ r} / \bar K) ⟶ 𝒪^{⊕ r} / K` is an
isomorphism. -/
instance : IsIso (closureComparison g K) := isIso_of_mono_of_epi _

/-- **The closure restricts back**: along a flat affine monomorphism of bases, the base change of
the closure of `K` is `K`. -/
theorem baseChange_closure : baseChange g (closure g K) = K := by
  unfold baseChange
  rw [← kernelSubobject_eq_of_comp_mono _ _ _ (baseChangeQuotientMap_closureComparison g K)]
  exact kernelSubobject_cokernel_π K

end Generic

end Closure

section BaseMorphism

variable {T' T : Scheme.{u}} (g : T' ⟶ T)

/-- The base change `ℙⁿ_{T'} ⟶ ℙⁿ_T` of a flat morphism `g` is flat. -/
theorem flat_projectiveSpaceOverMap [Flat g] : Flat (projectiveSpaceOverMap n g) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOverMap n g).flip inferInstance

/-- The base change `ℙⁿ_{T'} ⟶ ℙⁿ_T` of a monomorphism `g` is a monomorphism. -/
theorem mono_projectiveSpaceOverMap [Mono g] : Mono (projectiveSpaceOverMap n g) :=
  (isPullback_projectiveSpaceOverMap n g).flip.mono_snd_of_mono

/-- The base change `ℙⁿ_{T'} ⟶ ℙⁿ_T` of an affine morphism `g` is affine. -/
theorem isAffineHom_projectiveSpaceOverMap [IsAffineHom g] :
    IsAffineHom (projectiveSpaceOverMap n g) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOverMap n g).flip inferInstance

end BaseMorphism

/-! ### The generic point of a valuation ring -/

section ValuationRing

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The morphism `Spec K ⟶ Spec R` for `K` the fraction field of the domain `R`. -/
abbrev fractionFieldMap : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The morphism `Spec K ⟶ Spec R` is flat. -/
instance : Flat (fractionFieldMap R K) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))

/-- The morphism `Spec K ⟶ Spec R` is a monomorphism. -/
instance : Mono (fractionFieldMap R K) := by
  have : Epi (CommRingCat.ofHom (algebraMap R K)) := IsLocalization.epi (nonZeroDivisors R) K
  exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R K)).op

/-- A nonzero function on `Spec R` becomes a unit on `Spec K`. -/
theorem isUnit_fractionFieldMap_appTop {s : Γ(Spec (.of R), ⊤)} (hs : s ≠ 0) :
    IsUnit ((fractionFieldMap R K).appTop s) := by
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K))
  have h1 : (Scheme.ΓSpecIso (.of K)).hom ((fractionFieldMap R K).appTop s) =
      algebraMap R K ((Scheme.ΓSpecIso (.of R)).hom s) :=
    congrArg (fun φ => φ.hom s) hnat
  have h2 : (Scheme.ΓSpecIso (.of R)).hom s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg (Scheme.ΓSpecIso (.of R)).inv.hom h
  have h3 : IsUnit ((Scheme.ΓSpecIso (.of K)).hom ((fractionFieldMap R K).appTop s)) := by
    rw [h1]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero h2)).isUnit
  simpa using h3.map (Scheme.ΓSpecIso (.of K)).inv.hom

variable {R K}

/-- The image of a nonzero function on `Spec R` in the functions on `j⁻¹ U ⊆ ℙⁿ_K` is a unit. -/
theorem isUnit_projectiveSpaceOverMap_app_appLE (U : (projectiveSpaceOver n (Spec (.of R))).Opens)
    (hU : U ≤ (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) ⁻¹ᵁ ⊤)
    {s : Γ(Spec (.of R), ⊤)} (hs : s ≠ 0) :
    IsUnit ((projectiveSpaceOverMap n (fractionFieldMap R K)).app U
      (((projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)).appLE ⊤ U hU) s)) := by
  set j := projectiveSpaceOverMap n (fractionFieldMap R K)
  set fR := projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)
  set fK := projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)
  have hw : j ≫ fR = fK ≫ fractionFieldMap R K := projectiveSpaceOverMap_fst n _
  have e1 : fR.appLE ⊤ U hU ≫ j.app U = (j ≫ fR).appLE ⊤ (j ⁻¹ᵁ U)
      (le_rfl.trans ((TopologicalSpace.Opens.map j.base).map (homOfLE hU)).le) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have e2 : ∀ (φ ψ : projectiveSpaceOver n (Spec (.of K)) ⟶ Spec (.of R)) (h : φ = ψ) e,
      φ.appLE ⊤ (j ⁻¹ᵁ U) e = ψ.appLE ⊤ (j ⁻¹ᵁ U) (h ▸ e) := by
    rintro φ ψ rfl e
    rfl
  have e3 := congrArg (fun φ => φ.hom s) (e1.trans (e2 _ _ hw _))
  simp only [CommRingCat.comp_apply] at e3
  rw [e3, Scheme.Hom.comp_appLE]
  exact IsUnit.map (fK.appLE _ _ _).hom (isUnit_fractionFieldMap_appTop R K hs)

/-- **The quotient by the closure has no torsion over `R`**: on any open `U ⊆ ℙⁿ_R`, a nonzero
function on `Spec R` kills no nonzero section of `𝒪^{⊕ r} / \bar K`. The quotient embeds into
`j_*(𝒪^{⊕ r} / K)`, on whose sections the function acts through its image on `ℙⁿ_K`, a unit. -/
theorem eq_zero_of_smul_eq_zero_closure (K₀ : Subobject (freeModule n r (Spec (.of K))))
    (U : (projectiveSpaceOver n (Spec (.of R))).Opens)
    (hU : U ≤ (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) ⁻¹ᵁ ⊤)
    {s : Γ(Spec (.of R), ⊤)} (hs : s ≠ 0)
    (x : Γ(quotient (closure (fractionFieldMap R K) K₀), U))
    (h : ((projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)).appLE ⊤ U hU) s • x = 0) :
    x = 0 := by
  have hm : @Mono (SheafOfModules (projectiveSpaceOver n (Spec (.of R))).ringCatSheaf) _ _ _
      (closureQuotientι (fractionFieldMap R K) K₀) :=
    inferInstanceAs (Mono (closureQuotientι (fractionFieldMap R K) K₀))
  have hinj := Stacks.SheafOfModules.injective_app_of_mono
    (closureQuotientι (fractionFieldMap R K) K₀) (Opposite.op U)
  have e := Scheme.Modules.Hom.app_smul (closureQuotientι (fractionFieldMap R K) K₀)
    (((projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)).appLE ⊤ U hU) s) x
  rw [h, map_zero] at e
  have hx : (show Γ(quotient K₀, projectiveSpaceOverMap n (fractionFieldMap R K) ⁻¹ᵁ U) from
      (closureQuotientι (fractionFieldMap R K) K₀).app U x) = 0 :=
    ((isUnit_projectiveSpaceOverMap_app_appLE U hU hs).smul_eq_zero).mp e.symm
  exact hinj (hx.trans (map_zero _).symm)

/-- **The quotient by the closure is flat over a valuation ring** (Stacks 0539 on sections): on
every affine open of `ℙⁿ_R` its sections are torsion free over `Γ(Spec R) ≅ R`, a valuation
ring, so flat, and the affine-local criterion of Stacks 01U4 applies. -/
theorem isFlatOver_quotient_closure [ValuationRing R]
    (K₀ : Subobject (freeModule n r (Spec (.of K))))
    [(quotient K₀).IsQuasicoherent] :
    IsFlatOver (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)).toLRSHom.toShHom
      (quotient (closure (fractionFieldMap R K) K₀)) := by
  have : IsAffineHom (projectiveSpaceOverMap n (fractionFieldMap R K)) :=
    isAffineHom_projectiveSpaceOverMap _
  have hdom : IsDomain Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
  have hval : ValuationRing Γ(Spec (.of R), ⊤) :=
    Function.Surjective.valuationRing (Scheme.ΓSpecIso (.of R)).inv.hom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective
  refine ((isFlatOver_tfae (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
    (quotient (closure (fractionFieldMap R K) K₀))).out 4 1).mp ?_
  refine ⟨PUnit, fun _ => ⊤, iSup_const, fun _ => isAffineOpen_top _, fun _ => ?_⟩
  refine ⟨(projectiveSpaceOver n (Spec (.of R))).affineOpens,
    fun U : (projectiveSpaceOver n (Spec (.of R))).affineOpens => U.1, ?_,
    fun U => U.2, fun U => ?_⟩
  · rw [iSup_affineOpens_eq_top]
    rfl
  · intro _ _
    refine StacksDraft.GenericFibre.flat_of_isTorsionFree _ ?_
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro s x hsx
    exact (eq_or_ne s 0).imp_right fun hs => eq_zero_of_smul_eq_zero_closure K₀ U.1 _ hs x hsx

/-- **The quotient by the closure is of finite presentation** over a valuation ring: it is a
quasi-coherent quotient of `𝒪^{⊕ r}`, so of finite type, and flat over `R`
(`isFlatOver_quotient_closure`), and `Spec R` has a single weakly associated point, so
Stacks 05IK (on the whole flat locus, which is all of `ℙⁿ_R`) gives finite presentation. This is
where the source cites Stacks 0DLR. -/
theorem isFinitePresentation_quotient_closure [ValuationRing R]
    (K₀ : Subobject (freeModule n r (Spec (.of K)))) [(quotient K₀).IsQuasicoherent] :
    (quotient (closure (fractionFieldMap R K) K₀)).IsFinitePresentation := by
  have : IsAffineHom (projectiveSpaceOverMap n (fractionFieldMap R K)) :=
    isAffineHom_projectiveSpaceOverMap _
  have := isFiniteType_freeModule (n := n) (r := r) (Spec (.of R))
  have : @Epi (SheafOfModules (projectiveSpaceOver n (Spec (.of R))).ringCatSheaf) _ _ _
      (quotientπ (closure (fractionFieldMap R K) K₀)) :=
    inferInstanceAs (Epi (quotientπ (closure (fractionFieldMap R K) K₀)))
  have : (quotient (closure (fractionFieldMap R K) K₀)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi' (quotientπ (closure (fractionFieldMap R K) K₀))
  have : LocallyOfFinitePresentation (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)) :=
    (finitePresentation_projectiveSpaceOver n (Spec (.of R))).1
  have hS : ∀ s : Spec (.of R), ∃ W : (Spec (.of R)).Opens, s ∈ W ∧
      (Stacks.Divisors.schemeWeaklyAssociatedPoints (Spec (.of R)) ∩
        (W : Set (Spec (.of R)))).Finite :=
    fun _ => ⟨⊤, trivial,
      (schemeWeaklyAssociatedPoints_finite_of_isIntegral _).subset Set.inter_subset_left⟩
  exact isFinitePresentation_of_isOpenCover _ (fun _ : PUnit.{u + 1} => ⊤) iSup_const
    fun _ => isFinitePresentation_restrict_of_subset_flatLocus _ _ hS ⊤ fun x _ =>
      isFlatOver_quotient_closure (n := n) (r := r) (R := R) (K := K) K₀ x

end ValuationRing

/-! ### The existence part of the valuative criterion -/

open ProperFlatFibreEulerCharacteristic in
/-- **Existence part of the valuative criterion for `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}`** (the argument of
Stacks 0DM4 for the scheme-level functor `AlgebraicGeometry.ProjectiveQuot.hilbertFunctor`). Let
`R` be a valuation ring with fraction field `K`. Every `K`-point of `Quot^P` extends to an
`R`-point: for `K₀ ∈ Quot^P(Spec K)` there is `K₁ ∈ Quot^P(Spec R)` whose base change to `Spec K`
is `K₀`.

The extension is the closure `AlgebraicGeometry.ProjectiveQuot.closure`, the kernel of
`𝒪^{⊕ r} ⟶ j_*(𝒪^{⊕ r} / K₀)` on `ℙⁿ_R`. It restricts back to `K₀` because `j : ℙⁿ_K ⟶ ℙⁿ_R` is
a flat affine monomorphism; its quotient is flat because it is torsion free over the valuation
ring `R`, of finite presentation by Stacks 05IK, and has Hilbert polynomial `P` on every fibre
because `s ↦ χ(ℱ_s(d))` is locally constant (Stacks 0B9T) on the connected `Spec R` and equals
`P(d)` at the generic point. -/
@[ega "IV 2.8.1" "partial"]
theorem exists_baseChange_eq_of_valuationRing (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (K₀ : Subobject (freeModule n r (Spec (.of K))))
    (hK₀ : K₀ ∈ hilbertFamilies n r P (Spec (.of K))) :
    ∃ K₁ ∈ hilbertFamilies n r P (Spec (.of R)),
      baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K))) K₁ = K₀ := by
  obtain ⟨hfam₀, hP⟩ := hK₀
  have := hfam₀.1
  have : (quotient K₀).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_of_isFinitePresentation (quotient K₀)
  have := flat_projectiveSpaceOverMap (n := n) (fractionFieldMap R K)
  have := mono_projectiveSpaceOverMap (n := n) (fractionFieldMap R K)
  have := isAffineHom_projectiveSpaceOverMap (n := n) (fractionFieldMap R K)
  have hiso : IsIso (closureComparison (fractionFieldMap R K) K₀) := inferInstance
  let j := projectiveSpaceOverMap n (fractionFieldMap R K)
  let K₁ := closure (fractionFieldMap R K) K₀
  have hfp₁ : (quotient K₁).IsFinitePresentation := isFinitePresentation_quotient_closure K₀
  have hflat₁ := isFlatOver_quotient_closure (n := n) (R := R) (K := K) K₀
  have hfam₁ : IsFlatFamily (quotient K₁) := ⟨hfp₁, hflat₁⟩
  refine ⟨K₁, ⟨hfam₁, fun t => ?_⟩, baseChange_closure _ _⟩
  have := hfp₁
  have : (fibre t (quotient K₁)).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _ _
  refine ⟨inferInstance, fun d => ?_⟩
  rw [hilbertPolynomial_fibre_eq_fibreEulerCharacteristic hfam₁ t d]
  have hlc := isLocallyConstant_fibreEulerCharacteristic _
    (finitePresentation_projectiveSpaceOver n (Spec (.of R))) (twist d (quotient K₁))
    (isFinitePresentation_twist _ _ hfp₁) (isFlatOver_twist _ _ _ hflat₁)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  rw [hlc.apply_eq_of_preconnectedSpace t ((fractionFieldMap R K).base pt),
    ← eulerSum_eq_fibreEulerCharacteristic (isFlatFamily_twist hfam₁ d) K
      (fractionFieldMap R K) _ j (isPullback_projectiveSpaceOverMap n _) pt,
    ← eulerSum_congr _ _ (twistPullbackIso (fractionFieldMap R K) d (quotient K₁))]
  let e : twist d ((Scheme.Modules.pullback j).obj (quotient K₁)) ≅ twist d (quotient K₀) :=
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n (Spec (.of K))).toSheafedSpace.presheaf,
        (projectiveSpaceOver n (Spec (.of K))).toSheafedSpace.IsSheaf⟩)).mapIso
      (Iso.prod (@asIso _ _ _ _ (closureComparison (fractionFieldMap R K) K₀) hiso) (Iso.refl _))
  rw [eulerSum_congr _ _ e]
  obtain ⟨hcoh, hval⟩ := hP pt
  rw [← hval d, hilbertPolynomial_fibre_eq_fibreEulerCharacteristic hfam₀ pt d]
  have h3 := eulerSum_eq_fibreEulerCharacteristic (isFlatFamily_twist hfam₀ d) K (𝟙 _) _ (𝟙 _)
    (IsPullback.id_horiz _) pt
  have h4 := eulerSum_congr K (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
    ((Scheme.Modules.pullbackId _).app (twist d (quotient K₀)))
  exact congrArg (fun z : ℤ => (z : ℚ)) (h4.symm.trans h3)

end ProjectiveQuot

end AlgebraicGeometry

end
