module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckStepEight
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification

/-!
# `Hⁱ_c` of a direct image along a finite cover, Frobenius-equivariantly

Let `j_U : U ⟶ Ū` and `j_V : V ⟶ V̄` be compactifications over a finite field `k`, and let
`φ : V ⟶ U` be the restriction of an integral morphism `φ̄ : V̄ ⟶ Ū` over `k` with
`V = V̄ ×_Ū U`. For a bounded below complex `K` of sheaves of `Λ`-modules on `V_étale`,

`RΓ_c(V_k̄, K) ≅ RΓ_c(U_k̄, φ_* K)`,

naturally in `K` and compatibly with the canonical geometric Frobenius of the two sides:
`j_{U!} φ_* ≅ φ̄_* j_{V!}`
(`Stacks.EtaleCohomology.isIso_extensionByZeroDirectImageMap_of_isOpenImmersion`) and
`RΓ(Ū_k̄, φ̄_* -) = RΓ(V̄_k̄, -)` along the integral `φ̄`
(`Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso`).

For a connected finite étale cover `f : V ⟶ U` of a smooth curve and its smooth projective
compactification `V̄ ⟶ Ū` over the given compactification of `U`
(`AlgebraicGeometry.CoverCompactification`) this computes `Hⁱ_c(U_k̄, f_* A)` on the cover:
the first step of the proof of [Stacks, Tag 03VK].

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroDirectImageNatTrans`: `j_{U!} φ_* ⟶ φ̄_* j_{V!}`, natural.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIntegralIso`:
  `RΓ_c(V_k̄, K) ≅ RΓ_c(U_k̄, φ_* K)`.
* `AlgebraicGeometry.CoverCompactification.compactification`: `V ⟶ V̄` as a compactification of
  `V` over `k`.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIntegralIso_hom_naturality`,
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIntegralIso_hom_frobenius`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Natural

variable (Λ : Type) [CommRing Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

/-- **The canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)` is natural in `M`.** -/
def extensionByZeroDirectImageNatTrans :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ⟶
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb where
  app M := extensionByZeroDirectImageMap Λ j j' f fb sq M
  naturality M M' x := by
    apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
    dsimp only [Functor.comp_obj, Functor.comp_map, extensionByZeroDirectImageMap]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hu := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.naturality x
    have hr := (restrictionDirectImageIso Λ j j' f fb sq).hom.naturality
      ((etaleModuleExtensionByZero.{u, 0} Λ j').map x)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hr
    rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hr,
      Category.assoc]

/-- The component of `extensionByZeroDirectImageNatTrans` at `M` is the canonical map
`extensionByZeroDirectImageMap`. -/
@[simp]
lemma extensionByZeroDirectImageNatTrans_app (M : EtaleModules.{u, 0} Λ V) :
    (extensionByZeroDirectImageNatTrans Λ j j' f fb sq).app M =
      extensionByZeroDirectImageMap Λ j j' f fb sq M :=
  rfl

/-- The natural transformation `j_! f_* ⟶ f̄_* j'_!` is a natural isomorphism. -/
instance : IsIso (extensionByZeroDirectImageNatTrans Λ j j' f fb sq) :=
  haveI : ∀ M, IsIso ((extensionByZeroDirectImageNatTrans Λ j j' f fb sq).app M) := fun M =>
    isIso_extensionByZeroDirectImageMap_of_isOpenImmersion Λ j j' f fb sq M
  NatIso.isIso_of_isIso_app _

end Natural

section Integral

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {U V : Scheme.{u}}
  (fU : U ⟶ Spec (.of k)) (jU : CompactificationOf (Over.mk fU))
  (fV : V ⟶ Spec (.of k)) (jV : CompactificationOf (Over.mk fV))
  (φ : V ⟶ U) (φb : jV.space ⟶ jU.space) [IsIntegralHom φb] (hφb : φb ≫ jU.toBase = jV.toBase)
  (sq : IsPullback φ jV.immersion jU.immersion φb) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The integral morphism `φ̄ : V̄ ⟶ Ū` of compactifications, as a morphism over `k`. -/
abbrev integralCompactificationOverHom : Over.mk jV.toBase ⟶ Over.mk jU.toBase :=
  Over.homMk φb hφb

/-- The morphism of schemes underlying `integralCompactificationOverHom` is integral. -/
instance : IsIntegralHom (integralCompactificationOverHom fU jU fV jV φb hφb).left :=
  (inferInstance : IsIntegralHom φb)

/-- `φ̄_* j_{V!} K ≅ j_{U!} φ_* K`, degreewise on a bounded below complex. -/
def extensionByZeroDirectImageIntegralPlusIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ V)) :
    (etaleModuleDirectImage.{u, 0} Λ (integralCompactificationOverHom fU jU fV jV φb hφb).left
        ).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jV.immersion).mapCochainComplexPlus.obj K) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ jU.immersion).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (asIso (extensionByZeroDirectImageNatTrans Λ jU.immersion jV.immersion φ φb sq)).symm
      _).app K.obj)

/-- **`RΓ_c(V_k̄, K) ≅ RΓ_c(U_k̄, φ_* K)`** for the restriction `φ : V ⟶ U` of an integral morphism
`φ̄ : V̄ ⟶ Ū` of compactifications over `k` with `V = V̄ ×_Ū U`. -/
def compactSupportFrobeniusCohomologyIntegralIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ V)) :
    compactSupportFrobeniusCohomology.{u, 0} Λ fV jV kbar K ≅
      compactSupportFrobeniusCohomology.{u, 0} Λ fU jU kbar
        ((etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.obj K) :=
  frobeniusRestrictionDirectImageIso Λ (integralCompactificationOverHom fU jU fV jV φb hφb) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ jV.immersion).mapCochainComplexPlus.obj K) ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk jU.toBase).hom (specAlgebraMap k kbar))).mapIso
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk jU.toBase) kbar).mapIso
          (extensionByZeroDirectImageIntegralPlusIso Λ fU jU fV jV φ φb hφb sq K)))

/-- Pasting two commuting squares side by side. -/
private theorem comp_comp_eq_of_comm_of_comm {D : Type*} [Category D] {A₀ A₁ B₀ B₁ C₀ C₁ : D}
    (a : A₀ ⟶ A₁) (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁) (d : B₀ ⟶ B₁) (b₀ : B₀ ⟶ C₀) (b₁ : B₁ ⟶ C₁)
    (c : C₀ ⟶ C₁) (h₁ : a ≫ e₁ = e₀ ≫ d) (h₂ : d ≫ b₁ = b₀ ≫ c) :
    a ≫ e₁ ≫ b₁ = (e₀ ≫ b₀) ≫ c := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

omit [Fintype k] in
/-- **The identification `RΓ_c(V_k̄, K) ≅ RΓ_c(U_k̄, φ_* K)` is natural in `K`.** -/
theorem compactSupportFrobeniusCohomologyIntegralIso_hom_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ V)} (x : K ⟶ K') :
    (compactSupportFrobeniusFunctor.{u, 0} Λ fV jV kbar).map x ≫
        (compactSupportFrobeniusCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar K').hom =
      (compactSupportFrobeniusCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar K).hom ≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ fU jU kbar).map
          ((etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.map x) := by
  have h₁ := frobeniusRestrictionDirectImageIso_hom_naturality Λ
    (integralCompactificationOverHom fU jU fV jV φb hφb) kbar
    ((etaleModuleExtensionByZero.{u, 0} Λ jV.immersion).mapCochainComplexPlus.map x)
  have h₂ : (etaleModuleDirectImage.{u, 0} Λ
        (integralCompactificationOverHom fU jU fV jV φb hφb).left).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ jV.immersion).mapCochainComplexPlus.map x) ≫
        (extensionByZeroDirectImageIntegralPlusIso Λ fU jU fV jV φ φb hφb sq K').hom =
      (extensionByZeroDirectImageIntegralPlusIso Λ fU jU fV jV φ φb hφb sq K).hom ≫
        (etaleModuleExtensionByZero.{u, 0} Λ jU.immersion).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.map x) := by
    ext n : 2
    exact (asIso
      (extensionByZeroDirectImageNatTrans Λ jU.immersion jV.immersion φ φb sq)).inv.naturality
        (x.hom.f n)
  have h₃ := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk jU.toBase).hom (specAlgebraMap k kbar))).map
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk jU.toBase) kbar).map t))) h₂
  simp only [Functor.map_comp] at h₃
  exact comp_comp_eq_of_comm_of_comm _ _ _ _ _ _ _ h₁ h₃

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(V_k̄, K) ≅ RΓ_c(U_k̄, φ_* K)` commutes with the canonical geometric
Frobenius.** -/
theorem compactSupportFrobeniusCohomologyIntegralIso_hom_frobenius
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ V)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ fV jV kbar p q hcard K ≫
        (compactSupportFrobeniusCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar K).hom =
      (compactSupportFrobeniusCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar K).hom ≫
        canonicalCompactSupportFrobenius.{u, 0} Λ fU jU kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.obj K) := by
  have h₁ := frobeniusRestrictionDirectImageIso_hom_frobenius Λ
    (integralCompactificationOverHom fU jU fV jV φb hφb) kbar p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ jV.immersion).mapCochainComplexPlus.obj K)
  have h₂ := frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk jU.toBase) kbar p q
    hcard (extensionByZeroDirectImageIntegralPlusIso Λ fU jU fV jV φ φb hφb sq K).hom
  exact comp_comp_eq_of_comm_of_comm _ _ _ _ _ _ _ h₁ h₂.symm

end Integral

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.CoverCompactification

variable {k : Type u} [Field k] [PerfectField k] {U Ub V : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb] {jU : U ⟶ Ub}
  [IsOpenImmersion jU] {f : V ⟶ U} [IsFinite f] [Etale f] [ConnectedSpace V]
  (C : CoverCompactification k pUb jU f)

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
include C in
/-- `j ≫ q = f ≫ p_U`, from `j ≫ f̄ = f ≫ j_U` and `j_U ≫ p_Ū = p_U`. -/
lemma j_comp_q_of_eq (hjU : jU ≫ pUb = pU) : C.j ≫ C.q = f ≫ pU := by
  rw [← C.hq, reassoc_of% C.w, hjU]

/-- **The smooth projective compactification of a cover, as a compactification of `V` over `k`**
for the structure morphism `f ≫ p_U`. -/
def compactification (hjU : jU ≫ pUb = pU) : CompactificationOf (Over.mk (f ≫ pU)) :=
  ⟨StructuredArrow.mk (Y := Over.mk C.q)
      (Over.homMk (U := Over.mk (f ≫ pU)) (V := Over.mk C.q) C.j (C.j_comp_q_of_eq hjU)),
    ⟨C.isOpenImmersion, C.isProper⟩⟩

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
/-- The space of `C.compactification hjU` is `C.Vb`. -/
@[simp]
lemma compactification_space (hjU : jU ≫ pUb = pU) : (C.compactification hjU).space = C.Vb := rfl

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
/-- The open immersion of `C.compactification hjU` is `C.j`. -/
@[simp]
lemma compactification_immersion (hjU : jU ≫ pUb = pU) :
    (C.compactification hjU).immersion = C.j := rfl

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
/-- The structure morphism of `C.compactification hjU` to `Spec k` is `C.q`. -/
@[simp]
lemma compactification_toBase (hjU : jU ≫ pUb = pU) :
    (C.compactification hjU).toBase = C.q := rfl

end AlgebraicGeometry.CoverCompactification

end
