module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTripleCoordinates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison

/-!
# The Fourier transform of a point sheaf

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ`, `L = L_ψ(x)` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L)` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`, `μ(x, t) = xt`. For a rational point `c ∈ k` with inclusion `i_c : Spec k ⟶ 𝔸¹_k`
and a sheaf `N` of `Λ`-modules on `Spec k`,

`Φ(i_{c*} N) ≅ L_ψ(ct) ⊗ N_{𝔸¹}`,

a sheaf in degree `0`, `L_ψ(ct)` being the inverse image of `L` along the multiplication by `c`.
The fibre of `pr₁` over `c` is the section `s_c : t ↦ (c, t)` of `pr₂`; base change for `R i_{c!}`
along `pr₁` (Tag 0F7L), the projection formula for `s_c` and the locally free kernel, and the
composition of lower shriek functors (Tag 0F7J) reduce `Φ(i_{c*} N)` to
`R(pr₂ ∘ s_c)_!(N_{𝔸¹} ⊗ s_c⁻¹ μ⁻¹ L)`, and `pr₂ ∘ s_c = id`, `μ ∘ s_c = c ·`.

## Main definitions

* `Stacks.EtaleCohomology.affineLinePoint`: the rational point `c` of `𝔸¹_k`.
* `Stacks.EtaleCohomology.affineLineScale`: the multiplication by `c` on `𝔸¹_k`.
* `Stacks.EtaleCohomology.affineLinePointSection`: the section `t ↦ (c, t)` of `pr₂`.

## Main results

* `Stacks.EtaleCohomology.isPullback_affineLinePointSection`: the fibre of `pr₁` over `c`.
* `Stacks.EtaleCohomology.affineLinePointSection_comp_affineLineMul`: `μ ∘ s_c = c ·`.
* `Stacks.EtaleCohomology.nonempty_fourierTransform_affineLinePoint_iso`:
  `Φ(i_{c*} N) ≅ (N_{𝔸¹} ⊗ L_ψ(ct))[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier Stacks.Blowup

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

section Geometry

/-- **The rational point `c` of `𝔸¹_k`**, `Spec k ⟶ Spec k[X]`, `X ↦ c`. -/
def affineLinePoint (c : k) : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))

/-- A rational point of `𝔸¹_k` is a closed immersion. -/
instance isClosedImmersion_affineLinePoint (c : k) : IsClosedImmersion (affineLinePoint k c) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩

/-- **The multiplication by `c` on `𝔸¹_k`**, `X ↦ c X`. -/
def affineLineScale (c : k) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (Polynomial.C c * Polynomial.X)).toRingHom)

/-- The rational point `c` is a section of the structure morphism `𝔸¹_k ⟶ Spec k`. -/
theorem affineLinePoint_comp_structureMap (c : k) : affineLinePoint k c ≫ 𝔸f = 𝟙 _ := by
  have h : (Polynomial.evalRingHom c).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext a
    simp
  rw [affineLinePoint, affineLineStructureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h,
    CommRingCat.ofHom_id, Spec.map_id]

/-- **The section `s_c : t ↦ (c, t)` of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹`.** -/
def affineLinePointSection (c : k) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ pullback 𝔸f 𝔸f :=
  pullback.lift (𝔸f ≫ affineLinePoint k c) (𝟙 _) (by
    rw [Category.assoc, affineLinePoint_comp_structureMap, Category.comp_id, Category.id_comp])

/-- `pr₁ ∘ s_c` is the constant map `𝔸¹_k ⟶ Spec k ⟶ 𝔸¹_k` with value `c`. -/
@[reassoc]
theorem affineLinePointSection_fst (c : k) :
    affineLinePointSection k c ≫ pullback.fst 𝔸f 𝔸f = 𝔸f ≫ affineLinePoint k c :=
  pullback.lift_fst _ _ _

/-- `s_c` is a section of `pr₂`: `pr₂ ∘ s_c = id`. -/
@[reassoc]
theorem affineLinePointSection_snd (c : k) :
    affineLinePointSection k c ≫ pullback.snd 𝔸f 𝔸f = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- **The fibre of `pr₁ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` over the rational point `c`** is `𝔸¹_k`, through the
section `s_c`. -/
theorem isPullback_affineLinePointSection (c : k) :
    IsPullback (affineLinePointSection k c) 𝔸f (pullback.fst 𝔸f 𝔸f) (affineLinePoint k c) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd 𝔸f 𝔸f) (h₂₂ := 𝔸f) (v₁₃ := 𝔸f) ?_
    (affineLinePointSection_fst k c) (IsPullback.of_hasPullback 𝔸f 𝔸f).flip
  rw [affineLinePointSection_snd, affineLinePoint_comp_structureMap]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **`μ ∘ s_c = c ·`**: on the fibre over `c`, the Fourier kernel `xt` is `ct`. -/
theorem affineLinePointSection_comp_affineLineMul (c : k) :
    affineLinePointSection k c ≫ affineLineMul k = affineLineScale k c := by
  refine hom_ext_of_specHomRingHom ?_
  rw [specHomRingHom_comp, specHomRingHom_affineLineMul, affineLineScale, specHomRingHom_specMap]
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, Polynomial.algebraMap_eq]
    rw [← specHomRingHom_comp_apply, specHomRingHom_C, ← Category.assoc,
      affineLinePointSection_fst, Category.assoc, affineLinePoint_comp_structureMap,
      Category.comp_id, Category.id_comp]
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, map_mul, affineLineCoordinate]
    rw [← specHomRingHom_comp_apply, ← specHomRingHom_comp_apply, affineLinePointSection_fst,
      affineLinePointSection_snd, specHomRingHom_C, Category.id_comp, affineLinePoint,
      specHomRingHom_comp_specMap, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_X]

end Geometry

section Transform

variable [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **The Fourier transform of a point sheaf**: for a rational point `c` of `𝔸¹_k` and a sheaf `N`
of `Λ`-modules on `Spec k`, `Φ(i_{c*} N) ≅ (N_{𝔸¹} ⊗ L_ψ(ct))[0]`, `L_ψ(ct)` the inverse image of
`L_ψ(x)` along the multiplication by `c`. -/
theorem nonempty_fourierTransform_affineLinePoint_iso (j : CompactificationOf (Over.mk 𝔸f))
    (c : k) (N : EtaleModules.{u, 0} Λ (Spec (CommRingCat.of k))) :
    Nonempty ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ (affineLinePoint k c)).obj N)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ 𝔸f).obj N ⊗
          (etaleModuleInverseImage.{u, 0} Λ (affineLineScale k c)).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀))) := by
  let ic := affineLinePoint k c
  let sc := affineLinePointSection k c
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj L
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  have hsc𝓛 : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ sc).obj 𝓛) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_inverseImage Λ _ h𝓛)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  have : QuasiSeparatedSpace ↥(pullback 𝔸f 𝔸f) := quasiSeparatedSpace_of_quasiSeparated pr₂
  have pb := IsPullback.of_hasPullback 𝔸f 𝔸f
  have : LocallyOfFiniteType pr₂ := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    pb inferInstance
  have : IsSeparated pr₂ := MorphismProperty.of_isPullback (P := @IsSeparated) pb inferInstance
  have : IsClosedImmersion sc := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_affineLinePointSection k c).flip inferInstance
  have hsc : sc ≫ pr₂ = 𝟙 _ := affineLinePointSection_snd k c
  have : IsProper (sc ≫ pr₂) := by rw [hsc]; infer_instance
  have : IsIntegralHom (sc ≫ pr₂) := by rw [hsc]; infer_instance
  let sq := (isPullback_affineLinePointSection k c).flip
  let jc := CompactificationOf.ofProper ic
  let jsc := jc.baseChange sq
  let jP := j.baseChange pb
  let jid := CompactificationOf.ofProper (sc ≫ pr₂)
  let N0 :=
    (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (CommRingCat.of k))) 0).obj N
  let T𝓛 := etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e
  let Tsc := etaleModuleDerivedTensorRight Λ _ hsc𝓛
  let A := (etaleModuleInverseImage.{u, 0} Λ 𝔸f).obj N ⊗ (etaleModuleInverseImage.{u, 0} Λ sc).obj 𝓛
  let ea : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleDirectImage.{u, 0} Λ ic).obj N) ≅ (derivedLowerShriek.{u, 0} ic jc Λ).obj N0 :=
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} Λ ic) 0).app N ≪≫
      ((derivedLowerShriekOfProperIso Λ ic).app N0).symm
  let eb := (isoOfIsTorsionPlusι (derivedLowerShriekBaseChangeIso Λ sq jc)).app N0
  let ec := (isoOfIsTorsionPlusι ((derivedLowerShriekProjectionFormula Λ) sc jsc 𝓛 h𝓛 h𝓛e
    hsc𝓛).some).app ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ 𝔸f).obj N0)
  let ed := (isoOfIsTorsionPlusι (derivedLowerShriekCompIso Λ sc pr₂ jsc jP jid)).app (Tsc.obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ 𝔸f).obj N0))
  have := hsc𝓛.1
  have := hsc𝓛.2.1
  have := hsc𝓛.2.2
  let eT : Tsc.obj ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ 𝔸f).obj N0) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj A :=
    Tsc.mapIso ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ 𝔸f) 0).app N) ≪≫
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ sc).obj 𝓛)) 0).app _
  let ee : (derivedLowerShriek.{u, 0} (sc ≫ pr₂) jid Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj A :=
    (derivedLowerShriekOfProperIso Λ (sc ≫ pr₂)).app _ ≪≫
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} Λ (sc ≫ pr₂)) 0).app A).symm ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (eqToIso (by rw [hsc]) ≪≫ (etaleModuleDirectImageIdIso Λ _).app A)
  let eL : (etaleModuleInverseImage.{u, 0} Λ sc).obj 𝓛 ≅
      (etaleModuleInverseImage.{u, 0} Λ (affineLineScale k c)).obj L :=
    ((etaleModuleInverseImageCompIso Λ sc (affineLineMul k)).app L).symm ≪≫
      eqToIso (by rw [affineLinePointSection_comp_affineLineMul])
  exact ⟨(derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso (T𝓛.mapIso
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).mapIso ea ≪≫ eb) ≪≫
      ec.symm) ≪≫ ed.symm ≪≫
    (derivedLowerShriek.{u, 0} (sc ≫ pr₂) jid Λ).mapIso eT ≪≫
    ee ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((tensorLeft ((etaleModuleInverseImage.{u, 0} Λ 𝔸f).obj N)).mapIso eL)⟩

end Transform

end Stacks.EtaleCohomology

end
