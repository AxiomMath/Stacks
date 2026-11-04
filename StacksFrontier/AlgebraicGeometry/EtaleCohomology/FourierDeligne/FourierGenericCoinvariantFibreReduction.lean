module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantVanishingReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologyGeometricFibres

/-!
# Generic vanishing of `H²(Φ(j_! M[0]))`: reduction to the geometric fibres

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ`, `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`, and `M`
a sheaf of `Λ`-modules on an open `jV : V ⟶ 𝔸¹_k`. For a geometric point `s : Spec Ω ⟶ 𝔸¹_k` of
the second factor (the `t`-line), let `X_s` be the fibre of `pr₂` over `s` (a copy of `𝔸¹_Ω`, the
`x`-line), and `C_s = X_s ×_{𝔸¹_k} V` its open over `V` (a copy of `V_Ω`), with `t : C_s ⟶ V`.
Then

`s⁻¹ H²(Φ(j_! M[0])) ≅ H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s))`:

proper base change for `R pr₂!` on torsion complexes ([Stacks, Tag 0F7L]) gives the fibre
`H²_c(X_s, (pr₁⁻¹ j_! M ⊗ μ⁻¹ L_ψ)|_{X_s})`, and the open-closed triangle of
[Stacks, Tag 0GKP] for `C_s ⊆ X_s` identifies it with `H²_c(C_s, -)`, the integrand vanishing
on the closed complement, which lies over the complement of `V`.

So the generic vanishing of `H²(Φ(j_! M[0]))` on an open `U` of the `t`-line follows from the
vanishing of `H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s))` at the geometric points `s` of `U` at their
algebraically closed residue fields: this is the statement
`Stacks.EtaleCohomology.FourierFibreCoinvariantVanishingInput`, the generic vanishing of the
`π₁(V_Ω)`-coinvariants of the twisted monodromy `M ⊗ L_ψ(x s)`.

This is the second step of the proof of the input (L2) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.FourierFibreCoinvariantVanishingInput`.

## Main results

* `Stacks.EtaleCohomology.isZero_inverseImage_homology_derivedLowerShriek_of_geometricFibres`:
  `Hq(Rf_! K)` vanishes on an open `U` of the base when it vanishes on the geometric fibres over
  the points of `U`.
* `Stacks.EtaleCohomology.isZero_inverseImage_tensor_of_isZero_comp`.
* `Stacks.EtaleCohomology.fourierExtensionByZeroGenericVanishingInput_of_fibre`.
* `Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_fibre`.

## Implementation notes

The Fourier transform and `Rf_!` live in the standard model `HasDerivedCategory.standard`, and so
do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
  AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **`Hq(Rf_! K)` vanishes on an open `U` of the base when it vanishes on the geometric fibres
over `U`**, at the algebraic closures of the residue fields of the points of `U`, for `K` killed by
a positive integer: proper base change for `Rf_!` on `D⁺_tors` ([Stacks, Tag 0F7L]). -/
theorem isZero_inverseImage_homology_derivedLowerShriek_of_geometricFibres (Λ : Type) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m) (hK : m • 𝟙 K = 0)
    (q : ℤ) {U : Scheme.{u}} (jU : U ⟶ Y)
    (h : ∀ y : U, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} (pullback.snd f ((GeometricPoint.ofPoint U y).hom ≫ jU))
        (j.baseChange (IsPullback.of_hasPullback f ((GeometricPoint.ofPoint U y).hom ≫ jU))) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
          (pullback.fst f ((GeometricPoint.ofPoint U y).hom ≫ jU))).obj K)))) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj K))) := by
  refine isZero_of_forall_isZero_etaleModuleInverseImage Λ
    (fun y : U => (GeometricPoint.ofPoint U y).hom) (iUnion_range_geometricPoint_ofPoint U) _
    fun y => ?_
  let s := (GeometricPoint.ofPoint U y).hom ≫ jU
  let sq := IsPullback.of_hasPullback f s
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K
    (isTorsionPlus_of_nsmul_id_eq_zero K m hm hK)
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ s
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) q
  exact ((h y).of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)).symm ≪≫ e).symm).of_iso
    ((etaleModuleInverseImageCompIso Λ (GeometricPoint.ofPoint U y).hom jU).app _).symm

section Tensor

variable (Λ : Type) [CommRing Λ]

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal

/-- **`a⁻¹(p⁻¹ P ⊗ N) = 0` when `(a ≫ p)⁻¹ P = 0`**, for `- ⊗ a⁻¹ N` additive:
`a⁻¹(p⁻¹ P ⊗ N) ≅ (a ≫ p)⁻¹ P ⊗ a⁻¹ N`. -/
theorem isZero_inverseImage_tensor_of_isZero_comp {V Q Y : Scheme.{u}} (a : V ⟶ Q) (p : Q ⟶ Y)
    (P : EtaleModules.{u, 0} Λ Y) (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ (a ≫ p)).obj P))
    (N : EtaleModules.{u, 0} Λ Q)
    (hN : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ a).obj N)) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ a).obj
      ((etaleModuleInverseImage.{u, 0} Λ p).obj P ⊗ N)) := by
  have := hN.1
  exact ((MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ a).obj N)).map_isZero
    (hP.of_iso ((etaleModuleInverseImageCompIso Λ a p).app P).symm)).of_iso
    ((etaleModuleInverseImageTensorRightIso Λ a N).app _)

end Tensor

local notation "𝔸f" => affineLineStructureMap

/-- **(L2) on the geometric fibres**: for a sheaf `M` of `Λ`-modules on a nonempty open `V` of
`𝔸¹_k`, locally constant with finite values, there is a nonempty open `U` of the `t`-line such
that for every point `y` of `U`, with geometric point `s` at the algebraic closure of its residue
field, `H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s)) = 0`, where `C_s = X_s ×_{𝔸¹_k} V ≅ V_Ω` is the open over `V`
of the fibre `X_s` of `pr₂ : 𝔸¹ × 𝔸¹ ⟶ 𝔸¹` at `s`, `t : C_s ⟶ V` the projection, and
`L_ψ(x s)` the restriction of the Fourier kernel `μ⁻¹ L_ψ`; here `∑ ψ = 0` and `#k` is a unit
in the finite ring `Λ`. The group is the module of coinvariants of the twisted monodromy
representation `M_η̄ ⊗ L_ψ(x s)` of `π₁(V_Ω)`. -/
def FourierFibreCoinvariantVanishingInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
    (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X)),
    ∑ a : k, ψ a = 0 → IsUnit (Fintype.card k : Λ) →
    ∀ {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
      (M : EtaleModules.{u, 0} Λ V),
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) M →
      ∃ (U : Scheme.{u}) (jU : U ⟶ Spec (.of (Polynomial k))), IsOpenImmersion jU ∧ Nonempty U ∧
        ∀ (y : U) (jc : CompactificationOf (Over.mk
          (pullback.fst (pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
              ((GeometricPoint.ofPoint U y).hom ≫ jU) ≫ pullback.fst (𝔸f k) (𝔸f k)) jV ≫
            pullback.snd (pullback.snd (𝔸f k) (𝔸f k)) ((GeometricPoint.ofPoint U y).hom ≫ jU)))),
          IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
            ((derivedLowerShriek.{u, 0} _ jc Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleInverseImage.{u, 0} Λ
                  (pullback.snd (pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                    ((GeometricPoint.ofPoint U y).hom ≫ jU) ≫ pullback.fst (𝔸f k) (𝔸f k))
                      jV)).obj M ⊗
                (etaleModuleInverseImage.{u, 0} Λ
                  (pullback.fst (pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                      ((GeometricPoint.ofPoint U y).hom ≫ jU) ≫ pullback.fst (𝔸f k) (𝔸f k)) jV ≫
                    pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                      ((GeometricPoint.ofPoint U y).hom ≫ jU))).obj
                  ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
                    (affineLineArtinSchreierSheaf k Λ ψ B p₀))))))

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal in
/-- **(L2) for an extension by zero reduces to the geometric fibres**: `H²(Φ(j_! M[0]))` vanishes
on the open `U` of `Stacks.EtaleCohomology.FourierFibreCoinvariantVanishingInput`, its inverse
image at each geometric point `s` of `U` being `H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s))` (proper base change,
then the open-closed triangle for `C_s` in the fibre). -/
theorem fourierExtensionByZeroGenericVanishingInput_of_fibre
    (h : FourierFibreCoinvariantVanishingInput.{u}) :
    FourierExtensionByZeroGenericVanishingInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ hψ hq j V jV _ _ M hM
  obtain ⟨U, jU, hU, hUne, hfib⟩ := h k Λ ψ B p₀ hψ hq jV M hM
  refine ⟨U, jU, hU, hUne, ?_⟩
  let A := (etaleModuleExtensionByZero.{u, 0} Λ jV).obj M
  let pr₁ := pullback.fst (𝔸f k) (𝔸f k)
  let pr₂ := pullback.snd (𝔸f k) (𝔸f k)
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj A ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback (𝔸f k) (𝔸f k))
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app A) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, 0} Λ jU).mapIso
    ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso eT))
  have : LocallyOfFiniteType (𝔸f k) := locallyOfFiniteType_specPolynomial k
  refine isZero_inverseImage_homology_derivedLowerShriek_of_geometricFibres Λ pr₂ jP _
    (Nat.card Λ) Nat.card_pos ?_ 2 jU fun y => ?_
  · rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, natCard_nsmul_id_etaleModules Λ G, Functor.map_zero]
  let s := (GeometricPoint.ofPoint U y).hom ≫ jU
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  let j' := jP.baseChange (IsPullback.of_hasPullback pr₂ s)
  let ι := pullback.fst (u' ≫ pr₁) jV
  let t := pullback.snd (u' ≫ pr₁) jV
  let iZ := closedComplementι ι
  let G' := (etaleModuleInverseImage.{u, 0} Λ u').obj G
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj G'
  obtain ⟨a, b, c, hT⟩ := exists_distTriang_derivedLowerShriek_openClosed_plus Λ j' ι iZ
    (range_eq_compl_range_closedComplementι ι) K'
  -- the closed complement of `C_s` lies over the complement of `V`
  have hdisj : Disjoint (Set.range ((iZ ≫ u') ≫ pr₁).base) (Set.range jV.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨v, hv⟩
    have hz : iZ.base z ∈ Set.range ι.base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨v, by rw [hv, Category.assoc]; rfl⟩
    rw [range_eq_compl_range_closedComplementι ι] at hz
    exact hz ⟨z, rfl⟩
  have hNZ : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (iZ ≫ u')).obj 𝓛) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule
      (isLocallyFreeEtaleModule_inverseImage Λ (iZ ≫ u') h𝓛)
  have hGZ : IsZero ((etaleModuleInverseImage.{u, 0} Λ iZ).obj G') :=
    (isZero_inverseImage_tensor_of_isZero_comp Λ (iZ ≫ u') pr₁ A
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ _ jV hdisj M) 𝓛 hNZ).of_iso
      ((etaleModuleInverseImageCompIso Λ iZ u').app G).symm
  have h₃ : IsZero ((derivedLowerShriek.{u, 0} (iZ ≫ f') (j'.restrictClosed iZ) Λ).obj
      ((etaleModuleInverseImage.{u, 0} Λ iZ).mapDerivedCategoryPlus.obj K')) :=
    (derivedLowerShriek.{u, 0} (iZ ≫ f') (j'.restrictClosed iZ) Λ).map_isZero
      (((DerivedCategory.Plus.singleFunctor _ 0).map_isZero hGZ).of_iso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (etaleModuleInverseImage.{u, 0} Λ iZ) 0).app G'))
  have : IsIso a := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h₃
  -- the integrand on `C_s`
  let e₄ : (etaleModuleInverseImage.{u, 0} Λ (ι ≫ u')).obj
      ((etaleModuleInverseImage.{u, 0} Λ pr₁).obj A) ≅ (etaleModuleInverseImage.{u, 0} Λ t).obj M :=
    ((etaleModuleInverseImageCompIso Λ (ι ≫ u') pr₁).app A).symm ≪≫
      (etaleModuleInverseImageCompIso' Λ t jV ((ι ≫ u') ≫ pr₁)
        (by rw [Category.assoc]; exact pullback.condition)).app A ≪≫
      (etaleModuleInverseImage.{u, 0} Λ t).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jV).app A ≪≫
          (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jV).unit.app M)).symm)
  let eN : (etaleModuleRestriction.{u, 0} Λ ι).obj G' ≅
      (etaleModuleInverseImage.{u, 0} Λ t).obj M ⊗
        (etaleModuleInverseImage.{u, 0} Λ (ι ≫ u')).obj 𝓛 :=
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ ι).app G').symm ≪≫
      ((etaleModuleInverseImageCompIso Λ ι u').app G).symm ≪≫
      (etaleModuleInverseImageTensorRightIso Λ (ι ≫ u') 𝓛).app _ ≪≫
      MonoidalCategory.whiskerRightIso e₄ _
  have h₁ : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} (ι ≫ f') (j'.restrictOpen ι) Λ).obj
        ((etaleModuleRestriction.{u, 0} Λ ι).mapDerivedCategoryPlus.obj K'))) :=
    (hfib y (j'.restrictOpen ι)).of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
      ((derivedLowerShriek.{u, 0} (ι ≫ f') (j'.restrictOpen ι) Λ).mapIso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (etaleModuleRestriction.{u, 0} Λ ι) 0).app G' ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso eN)))
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app G)))
  exact h₁.of_iso ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso (asIso a)).symm

/-- **(L2) reduces to the geometric fibres**:
`Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput` follows from the generic vanishing
of the coinvariants `H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s))`. -/
theorem fourierGenericCoinvariantVanishingInput_of_fibre
    (h : FourierFibreCoinvariantVanishingInput.{u}) :
    FourierGenericCoinvariantVanishingInput.{u} :=
  fourierGenericCoinvariantVanishingInput_of_extensionByZero
    (fourierExtensionByZeroGenericVanishingInput_of_fibre h)

end Stacks.EtaleCohomology

end
