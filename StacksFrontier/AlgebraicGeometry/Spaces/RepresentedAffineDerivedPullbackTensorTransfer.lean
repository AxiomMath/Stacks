module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackTensorCompat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapTensorProduct

/-!
# Stacks 0DKH for derived tensor products on affine representables

For a commutative square `g₀' ≫ f₀ = f₀' ≫ g₀` of objects of the big fppf site with affine
underlying schemes, with rings of global functions `R = Γ(V)`, `A = Γ(U)`, `R' = Γ(V')` and
`A' = Γ(U')`, if the composite of Stacks 0DKH attached to `Φ_A M`, `Φ_{A'} M'` and
`L(g')^*Φ_A M ≅ Φ_{A'}(M ⊗ᴸ_A A') ⟶ Φ_{A'} M'` is invertible, then so is the composite attached to
`Φ_A E ⊗ᴸ Φ_A M`, `L(g')^*Φ_A E ⊗ᴸ Φ_{A'} M'` and Stacks 07A4 followed by
`L(g')^*Φ_A E ⊗ᴸ (-)`: the tensor step of Stacks 0DKI (1) on affine representables.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_tensor`: the tensor step for
  quasi-coherent complexes `E`, `K` on `U` and `K'` on `U'`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_tensor_iff_of_iso`: the
  composite of Stacks 0DKH attached to Stacks 07A4 followed by `L(g')^*E ⊗ᴸ φ` only depends on
  `E`, `K`, `K'`, `φ` up to isomorphism.
* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_tensor_of_kFlat`: the case of
  K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_tensor_of_compat`: the same from
  the compatibility of Stacks 07A4 with `β` up to a unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.Generic

/-- The bookkeeping of the transfer of Stacks 0DKH along Stacks 07A4, for arbitrary morphisms:
the compatibility `hD` of 07A4 with the base change isomorphism up to a central `s₃`, moved past
`m` by the naturality squares `h₁`, `h₂`, `hB`. -/
theorem tensorTransfer_chain_eq {C : Type*} {_ : Category C}
    {o₀ o₁ o₂ o₃ o₄ q₁ q₂ q₃ q₄ q₅ q₆ : C}
    (lb : o₀ ⟶ o₁) (bt : o₁ ⟶ o₂) (ei : o₂ ⟶ o₃) (m : o₃ ⟶ o₄) (s₃ : o₃ ⟶ o₃) (s₄ : o₄ ⟶ o₄)
    (t : o₀ ⟶ q₁) (x₁ : q₁ ⟶ q₂) (y₁ : q₂ ⟶ q₃) (b₁ : q₃ ⟶ o₃) (y₁' : q₁ ⟶ q₄)
    (x₁' : q₄ ⟶ q₃) (z' : q₄ ⟶ q₅) (x₂ : q₅ ⟶ q₆) (z : q₃ ⟶ q₆) (b₂ : q₆ ⟶ o₄)
    (φ₁ : o₁ ⟶ o₄) (ψ : q₁ ⟶ q₅)
    (hφ₁ : φ₁ = bt ≫ ei ≫ m ≫ s₄) (hψ : ψ = y₁' ≫ z')
    (hD : lb ≫ bt ≫ ei ≫ s₃ = t ≫ x₁ ≫ y₁ ≫ b₁) (hs : m ≫ s₄ = s₃ ≫ m)
    (h₁ : x₁ ≫ y₁ = y₁' ≫ x₁') (h₂ : x₁' ≫ z = z' ≫ x₂) (hB : b₁ ≫ m = z ≫ b₂) :
    lb ≫ φ₁ = (t ≫ ψ) ≫ x₂ ≫ b₂ := by
  rw [hφ₁, hψ, hs]
  simp only [Category.assoc]
  rw [reassoc_of% hD, reassoc_of% h₁, hB, reassoc_of% h₂]

/-- A unit `c` acts invertibly on every object of an `R`-linear category. -/
theorem isIso_smul_id_of_isUnit' {R : Type*} [CommRing R] {C : Type*} {_ : Category C}
    [Preadditive C] [Linear R C] {c : R} (hc : IsUnit c) (X : C) : IsIso (c • 𝟙 X) :=
  ⟨⟨((hc.unit⁻¹ : Rˣ) : R) • 𝟙 X,
    by rw [Linear.smul_comp, Category.id_comp, smul_smul, IsUnit.mul_val_inv, one_smul],
    by rw [Linear.smul_comp, Category.id_comp, smul_smul, IsUnit.val_inv_mul, one_smul]⟩⟩

/-- `r ≫ F(a ≫ a' ≫ s)` is invertible when `r ≫ F(a ≫ a')` and `s` are. -/
theorem isIso_comp_map_comp_comp {C D : Type*} {_ : Category C} {_ : Category D} (F : C ⥤ D)
    {Y : D} {A B B' : C} (r : Y ⟶ F.obj A) (a : A ⟶ B) (a' : B ⟶ B') (s : B' ⟶ B')
    (h : IsIso (r ≫ F.map (a ≫ a'))) (hs : IsIso s) : IsIso (r ≫ F.map (a ≫ a' ≫ s)) := by
  rw [← Category.assoc a a' s, F.map_comp, ← Category.assoc]
  infer_instance

/-- The bookkeeping of the transport of Stacks 07A4 followed by `E ⊗ᴸ φ` along isomorphisms. -/
theorem tensorTransport_square {C : Type*} {_ : Category C} {o₀ o₁ o₂ o₃ q₁ q₂ q₃ q₄ : C}
    (Lm : o₀ ⟶ o₁) (t₁ : o₁ ⟶ o₂) (p₁ : o₂ ⟶ o₃) (t : o₀ ⟶ q₁) (u : q₁ ⟶ q₂) (v : q₂ ⟶ o₂)
    (q : q₂ ⟶ q₃) (r : q₃ ⟶ o₃) (s : q₁ ⟶ q₄) (u' : q₄ ⟶ q₃)
    (hn : Lm ≫ t₁ = t ≫ u ≫ v) (hv : v ≫ p₁ = q ≫ r) (hu : u ≫ q = s ≫ u') :
    Lm ≫ t₁ ≫ p₁ = (t ≫ s) ≫ u' ≫ r := by
  rw [reassoc_of% hn, hv, reassoc_of% hu, Category.assoc]

/-- The bookkeeping of the transport of the map attached to `φ` along the counit and a K-flat
model. -/
theorem counitTransport_square {C : Type*} {_ : Category C} {o₀ o₁ o₂ o₃ q₁ q₂ q₃ : C}
    (Lb : o₀ ⟶ o₂) (l₁ : o₀ ⟶ o₁) (l₂ : o₁ ⟶ o₂) (φ : o₂ ⟶ o₃) (β₀ : o₁ ⟶ q₂) (m₀ : q₂ ⟶ q₃)
    (ε : q₃ ⟶ o₃) (β₁ : o₀ ⟶ q₁) (dN : q₁ ⟶ q₂) (mm : q₁ ⟶ q₃) (φ₁ : o₀ ⟶ q₃)
    (hm : Lb = l₁ ≫ l₂) (hs : l₂ ≫ φ = β₀ ≫ m₀ ≫ ε) (hn : l₁ ≫ β₀ = β₁ ≫ dN)
    (hφ₁ : φ₁ = β₁ ≫ mm) (hmm : mm = dN ≫ m₀) : Lb ≫ φ = φ₁ ≫ ε := by
  rw [hm, hφ₁, hmm, Category.assoc, hs, ← Category.assoc l₁, hn]
  simp only [Category.assoc]

end Stacks.Generic

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

/-- The compatibility of Stacks 07A4 with `β` up to the scalar `c`, moved past
`φ₀ : N ⊗ᴸ_A A' ⟶ M'`: the square comparing the composite of Stacks 07A4 with
`L(g')^*Φ P ⊗ᴸ (β ≫ Φ'φ₀)` and the base change isomorphism at `P ⊗ᴸ N` followed by
`Φ'((P ⊗ᴸ A') ⊗ᴸ φ₀)` and `c`. -/
theorem representedAffineTensorTransfer_eq (P N :
    CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj N) ⟶ M') (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (hD : ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        (((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N))))) =
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
        (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).app
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((representedAffineToposDerivedAssociated B S hS U').obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P)))).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj N))) ≫
        (((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N)))) :
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        (((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
        (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj N))) ≫ ((representedAffineToposDerivedBaseChangeIso B S
        hS g₀').hom.app (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N)) ≫ (representedAffineToposDerivedAssociated B S hS U').map
        ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).map
        φ₀ ≫ (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') :
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') ⟶
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M')))) = (((smallEtaleDerivedPullbackTensorIso
        (representedSpaceMap B S hS g₀')).hom.app
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
        (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map φ₀))) ≫ (((smallEtaleDerivedTensor B
        S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).app
        ((representedAffineToposDerivedAssociated B S
        hS U').obj M')) ≫ (((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).app M') := by
  exact Stacks.Generic.tensorTransfer_chain_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (congrArg (_ ≫ ·) (((representedAffineToposDerivedAssociated B S hS U').map_comp _ _).trans
      (congrArg (_ ≫ ·) ((representedAffineToposDerivedAssociated B S hS U').map_comp _ _))))
    (Functor.map_comp _ _ _) hD (Stacks.Generic.map_smul_id_comp _ _ c).symm
    (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).naturality
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj N))).symm
    (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).naturality
      ((representedAffineToposDerivedAssociated B S hS U').map φ₀)).symm
    (((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
      ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).naturality φ₀).symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
include w₀ in
/-- The ring side of the tensor step: Stacks 0DKI (1) at the ring level, followed by the unit
`c`. -/
theorem isIso_representedAffineTensorTransfer_ring (P N :
    CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj N) ⟶ M') (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) (hcu :
        IsUnit c)
    (hφ : IsIso ((RingTheory.TorIndependence.ringHomSquareComparison
        (representedAffineCommRingCatHom B S hS f₀).hom
        (representedAffineCommRingCatHom B S hS g₀).hom
        (representedAffineCommRingCatHom B S hS g₀').hom
        (representedAffineCommRingCatHom B S hS f₀').hom
        ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS f₀' g₀))).app (DerivedCategory.Q.obj N) ≫
        (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S
        hS f₀').hom).mapDerivedCategory.map φ₀)) :
    IsIso ((RingTheory.TorIndependence.ringHomSquareComparison
        (representedAffineCommRingCatHom B S hS f₀).hom
        (representedAffineCommRingCatHom B S hS g₀).hom
        (representedAffineCommRingCatHom B S hS g₀').hom
        (representedAffineCommRingCatHom B S hS f₀').hom
        ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS f₀' g₀))).app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N)) ≫
      (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S
          hS f₀').hom).mapDerivedCategory.map ((RingTheory.TorIndependence.extensionTensorIso
          (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
          ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)) ≫
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
          ((representedAffineDerivedExtension B S hS g₀').functor.obj
          (DerivedCategory.Q.obj P))).map φ₀ ≫
          (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
          ((representedAffineDerivedExtension B S hS g₀').functor.obj
          (DerivedCategory.Q.obj P))).obj M') :
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
          ((representedAffineDerivedExtension B S hS g₀').functor.obj
          (DerivedCategory.Q.obj P))).obj M') ⟶
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
          ((representedAffineDerivedExtension B S hS g₀').functor.obj
          (DerivedCategory.Q.obj P))).obj M')))) := by
  refine Stacks.Generic.isIso_comp_map_comp_comp
    (ModuleCat.restrictScalars
        (representedAffineCommRingCatHom B S hS f₀').hom).mapDerivedCategory _ _ _ _ ?_ ?_
  · exact (RingTheory.TorIndependence.isIso_ringHomSquareComparison_derivedTensor
      (representedAffineCommRingCatHom B S hS f₀).hom (representedAffineCommRingCatHom B S
          hS g₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom (representedAffineCommRingCatHom B S
          hS f₀').hom
      ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS
            f₀' g₀)) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) φ₀ hφ)
  · exact Stacks.Generic.isIso_smul_id_of_isUnit' hcu _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
include w₀ in
/-- Stacks 0DKH for `Φ P ⊗ᴸ Φ N` is invertible exactly when it is for `Φ(P ⊗ᴸ N)`, along
`Φ P ⊗ᴸ Φ N ≅ Φ(P ⊗ᴸ N)` and the compatibility of Stacks 07A4 with `β` up to `c`. -/
theorem isIso_representedAffineTensorTransfer_iff
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N) ⟶ M')
    (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
    (hD : ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        (((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N))))) =
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
        (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).app
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((representedAffineToposDerivedAssociated B S hS U').obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P)))).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj N))) ≫
        (((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N)))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P))).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).obj
          ((representedAffineToposDerivedAssociated B S hS U').obj M'))
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
              (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
              ((representedAffineToposDerivedAssociated B S hS U).obj
                  (DerivedCategory.Q.obj P)))).map
            ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
                (DerivedCategory.Q.obj N) ≫
              (representedAffineToposDerivedAssociated B S hS U').map φ₀))) ↔
      IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        ((representedAffineToposDerivedAssociated B S hS U).obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
            (DerivedCategory.Q.obj N)))
        ((representedAffineToposDerivedAssociated B S hS U').obj
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
            ((representedAffineDerivedExtension B S hS g₀').functor.obj
            (DerivedCategory.Q.obj P))).obj M'))
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
            (DerivedCategory.Q.obj N)) ≫ (representedAffineToposDerivedAssociated B S hS U').map
            ((RingTheory.TorIndependence.extensionTensorIso
            (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
            ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)) ≫
            ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
            ((representedAffineDerivedExtension B S hS g₀').functor.obj
            (DerivedCategory.Q.obj P))).map φ₀ ≫
            (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
            ((representedAffineDerivedExtension B S hS g₀').functor.obj
            (DerivedCategory.Q.obj P))).obj M') :
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
            ((representedAffineDerivedExtension B S hS g₀').functor.obj
            (DerivedCategory.Q.obj P))).obj M') ⟶
            (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
            ((representedAffineDerivedExtension B S hS g₀').functor.obj
            (DerivedCategory.Q.obj P))).obj M'))))) :=
  isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS (representedSpaceMap B S hS f₀)
    (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
    (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
    (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P))).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))
    (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).obj
        ((representedAffineToposDerivedAssociated B S hS U').obj M'))
    (((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
        (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map φ₀)))
    ((representedAffineToposDerivedAssociated B S hS U).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N)))
    ((representedAffineToposDerivedAssociated B S hS U').obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M'))
    ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N)) ≫ (representedAffineToposDerivedAssociated B S hS U').map
        ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).map
        φ₀ ≫ (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') :
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') ⟶
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M'))))
    (((representedAffineDerivedTensorBifunctorIso B S hS U).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj N))
    ((((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).mapIso
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').app (DerivedCategory.Q.obj P))).app
        ((representedAffineToposDerivedAssociated B S hS U').obj M')) ≪≫
        ((representedAffineDerivedTensorBifunctorIso B S hS U').app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).app M')
    (representedAffineTensorTransfer_eq B S hS g₀' P N M' φ₀ c hD)

include w₀ in
/-- The tensor step of Stacks 0DKI (1) on affine representables, from the compatibility of
Stacks 07A4 with `β` up to a unit `c`. -/
theorem isIso_representedAffineBaseChangeComp_tensor_of_compat
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N) ⟶ M')
    (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) (hcu : IsUnit c)
    (hD : ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        (((representedAffineDerivedTensorBifunctorIso B S hS U).hom.app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))) ≫
        ((representedAffineToposDerivedAssociated B S hS U').map
        (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N))))) =
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
        (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj P))).app
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))) ≫
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
        ((representedAffineToposDerivedAssociated B S hS U').obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P)))).map
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
        (DerivedCategory.Q.obj N))) ≫
        (((representedAffineDerivedTensorBifunctorIso B S hS U').hom.app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).app
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N))))
    (hφ : IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))
        ((representedAffineToposDerivedAssociated B S hS U').obj M')
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
          (representedAffineToposDerivedAssociated B S hS U').map φ₀))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P))).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).obj
          ((representedAffineToposDerivedAssociated B S hS U').obj M'))
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
              (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
              ((representedAffineToposDerivedAssociated B S hS U).obj
                  (DerivedCategory.Q.obj P)))).map
            ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
                (DerivedCategory.Q.obj N) ≫
              (representedAffineToposDerivedAssociated B S hS U').map φ₀))) := by
  refine (isIso_representedAffineTensorTransfer_iff B S hS f₀ g₀ f₀' g₀' w₀ P N M' φ₀ c
    hD).mpr ?_
  have key2 := isIso_representedAffineBaseChangeComp_iff B S hS f₀ g₀ f₀' g₀' w₀
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).tensor.obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj N)) (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M')
    ((RingTheory.TorIndependence.extensionTensorIso
        (representedAffineCommRingCatHom B S hS g₀').hom).iso.inv.app
        ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj P))).map
        φ₀ ≫ (c • 𝟙 (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') :
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M') ⟶
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)).tensor.obj
        ((representedAffineDerivedExtension B S hS g₀').functor.obj
        (DerivedCategory.Q.obj P))).obj M')))
  refine key2.mpr ?_
  exact isIso_representedAffineTensorTransfer_ring B S hS f₀ g₀ f₀' g₀' w₀ P N M' φ₀ c hcu
    ((isIso_representedAffineBaseChangeComp_iff B S hS f₀ g₀ f₀' g₀' w₀ (DerivedCategory.Q.obj N)
        M' φ₀).mp hφ)

include w₀ in
/-- **The tensor step of Stacks 0DKI (1) on affine representables, on K-flat models.** For K-flat
complexes `P`, `N` of `A`-modules with flat terms and `φ₀ : N ⊗ᴸ_A A' ⟶ M'`: if the composite of
Stacks 0DKH attached to `Φ_A N`, `Φ_{A'} M'` and `L(g')^*Φ_A N ≅ Φ_{A'}(N ⊗ᴸ_A A') ⟶ Φ_{A'} M'` is
invertible, so is the one attached to `Φ_A P ⊗ᴸ Φ_A N`, `L(g')^*Φ_A P ⊗ᴸ Φ_{A'} M'` and Stacks 07A4
followed by `L(g')^*Φ_A P ⊗ᴸ (-)`. -/
theorem isIso_representedAffineBaseChangeComp_tensor_of_kFlat
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hP : P.KFlat) (hN : N.KFlat)
    (hPf : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X n))
    (hNf : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X n))
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ₀ : (representedAffineDerivedExtension B S hS g₀').functor.obj (DerivedCategory.Q.obj N) ⟶ M')
    (hφ : IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))
        ((representedAffineToposDerivedAssociated B S hS U').obj M')
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
          (representedAffineToposDerivedAssociated B S hS U').map φ₀))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P))).obj
          ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)))
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P)))).obj
          ((representedAffineToposDerivedAssociated B S hS U').obj M'))
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
            ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj P),
              (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
              ((representedAffineToposDerivedAssociated B S hS U).obj
                  (DerivedCategory.Q.obj P)))).map
            ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
                (DerivedCategory.Q.obj N) ≫
              (representedAffineToposDerivedAssociated B S hS U').map φ₀))) :=
  (exists_representedAffineDerivedPullbackTensorCompat B S hS g₀').elim fun c hc =>
    isIso_representedAffineBaseChangeComp_tensor_of_compat B S hS f₀ g₀ f₀' g₀' w₀ P N M' φ₀ c hc.1
      (hc.2 P N hP hN hPf hNf) hφ

section Transport

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The composite of Stacks 0DKH attached to Stacks 07A4 followed by `L(g')^*E ⊗ᴸ φ` only
depends on `E`, `K`, `K'` and `φ` up to isomorphism.** -/
theorem isIso_smallEtaleDerivedBaseChangeComp_tensor_iff_of_iso (w : g' ≫ f = f' ≫ g)
    (E K E₁ K₁ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' K₁' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (a : E ≅ E₁) (b : K ≅ K₁) (b' : K' ≅ K₁')
    (h : (smallEtaleDerivedModulePullback B S hS g').map b.hom ≫ φ₁ = φ ≫ b'.hom) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
        (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')
        ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
          ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ)) ↔
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w
        (((smallEtaleDerivedTensor B S hS X).obj E₁).obj K₁)
        (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E₁)).obj K₁')
        ((smallEtaleDerivedPullbackTensorIso g').hom.app (E₁, K₁) ≫
          ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E₁)).map φ₁)) :=
  isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS f g f' g' w _ _ _ _ _ _
    (((smallEtaleDerivedTensor B S hS X).mapIso a).app K ≪≫
      ((smallEtaleDerivedTensor B S hS X).obj E₁).mapIso b)
    (((smallEtaleDerivedTensor B S hS X').mapIso
        ((smallEtaleDerivedModulePullback B S hS g').mapIso a)).app K' ≪≫
      ((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E₁)).mapIso b')
    (Stacks.Generic.tensorTransport_square _ _ _ _ _ _ _ _ _ _
      ((smallEtaleDerivedPullbackTensorIso g').hom.naturality (X := (E, K)) (Y := (E₁, K₁))
        ⟨a.hom, b.hom⟩)
      (((Functor.map_comp _ _ _).symm.trans (congrArg _ h)).trans (Functor.map_comp _ _ _))
      ((((smallEtaleDerivedTensor B S hS X').map
        ((smallEtaleDerivedModulePullback B S hS g').map a.hom)).naturality φ).symm))

end Transport

section RepresentedTensor

include w₀ in
/-- The tensor step of Stacks 0DKI (1) on affine representables, through K-flat models `P`, `N`
of `RΓ(U, E)`, `RΓ(U, K)` with flat terms. For quasi-coherent `E`, `K`
on `U`, `K'` on `U'` and `φ : L(g')^*K ⟶ K'`: if the composite of Stacks 0DKH attached to
`(K, K', φ)` is invertible, so is the one attached to `(E ⊗ᴸ K, L(g')^*E ⊗ᴸ K')` and Stacks 07A4
followed by `L(g')^*E ⊗ᴸ φ`. -/
theorem isIso_representedAffineBaseChangeComp_tensor_of_model
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E)
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hK' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K')
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K')
    (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hP : P.KFlat) (hN : N.KFlat)
    (hPf : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X n))
    (hNf : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X n))
    (eP : DerivedCategory.Q.obj P ≅ (representedAffineDerivedSections B S hS U).obj E)
    (eN : DerivedCategory.Q.obj N ≅ (representedAffineDerivedSections B S hS U).obj K)
    (hφ : IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        K K' φ)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj E).obj K)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj E)).obj K')
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app (E, K) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS
                (representedSpaceMap B S hS g₀')).obj E)).map φ)) := by
  have hεE := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  have hεK := isIso_representedAffineDerivedAdjunction_counit_app B S hS U K hK
  have hεK' := isIso_representedAffineDerivedAdjunction_counit_app B S hS U' K' hK'
  let aE := (representedAffineToposDerivedAssociated B S hS U).mapIso eP ≪≫
    @asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app E) hεE
  let aK := (representedAffineToposDerivedAssociated B S hS U).mapIso eN ≪≫
    @asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app K) hεK
  let aK' := @asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U').counit.app K') hεK'
  let φ₀ := representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ
  have h : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
      ((representedAffineToposDerivedAssociated B S hS U).map eN.hom ≫
        (representedAffineDerivedAdjunction B S hS U).counit.app K) ≫ φ =
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((representedAffineDerivedExtension B S hS g₀').functor.map eN.hom ≫ φ₀)) ≫
        (representedAffineDerivedAdjunction B S hS U').counit.app K' :=
    Stacks.Generic.counitTransport_square _ _ _ _ _ _ _ _ _ _ _
      (Functor.map_comp _ _ _)
      (representedAffineSectionsBaseChangeMap_spec B S hS g₀' K K' φ)
      ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.naturality eN.hom)
      rfl (Functor.map_comp _ _ _)
  have h1 := (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) _ _ _ _ _ φ aK aK' h).mpr hφ
  have h2 := isIso_representedAffineBaseChangeComp_tensor_of_kFlat B S hS f₀ g₀ f₀' g₀' w₀ P N
    hP hN hPf hNf _ _ h1
  exact (isIso_smallEtaleDerivedBaseChangeComp_tensor_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) _ _ E K _ K' _ φ aE aK aK' h).mp h2

include w₀ in
/-- **The tensor step of Stacks 0DKI (1) on affine representables.** For quasi-coherent `E`, `K`
on `U`, `K'` on `U'` and `φ : L(g')^*K ⟶ K'`: if the composite of Stacks 0DKH attached to
`(K, K', φ)` is invertible, so is the one attached to `(E ⊗ᴸ K, L(g')^*E ⊗ᴸ K')` and Stacks 07A4
followed by `L(g')^*E ⊗ᴸ φ`. -/
theorem isIso_representedAffineBaseChangeComp_tensor
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E)
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hK' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K')
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K')
    (hφ : IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        K K' φ)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj E).obj K)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj E)).obj K')
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app (E, K) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS
                (representedSpaceMap B S hS g₀')).obj E)).map φ)) := by
  have key : ∀ Y, ∃ P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ,
      P.KFlat ∧ (∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X n)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ Y) := fun Y => by
    obtain ⟨P, p, hp⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
      (DerivedCategory.Q.objPreimage Y)
    have : QuasiIso p := hp.2.2.1
    exact ⟨P, hp.1, hp.2.1, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso _⟩⟩
  obtain ⟨P, hP, hPf, ⟨eP⟩⟩ := key ((representedAffineDerivedSections B S hS U).obj E)
  obtain ⟨N, hN, hNf, ⟨eN⟩⟩ := key ((representedAffineDerivedSections B S hS U).obj K)
  exact isIso_representedAffineBaseChangeComp_tensor_of_model B S hS f₀ g₀ f₀' g₀' w₀
    E K hE hK K' hK' φ P N hP hN hPf hNf eP eN hφ

end RepresentedTensor

end AlgebraicGeometry.Space
