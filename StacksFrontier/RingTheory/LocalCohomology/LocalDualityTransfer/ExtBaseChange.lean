module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Naturality of the derived-Hom base-change map

The base-change morphism `RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` of Stacks 0E1X
(`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange`) is natural in `K`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u uR uA uM

namespace Stacks.DerivedHom.ExtensionOfScalars

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The derived-Hom base-change map is natural in the source.** -/
theorem derivedHomBaseChange_naturality_left :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    {K K' : DerivedCategory (ModuleCat.{max uR uA uM} R)} (g : K' ⟶ K)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
    F.map ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R).map
        (show (op K, M) ⟶ (op K', M) from (g.op, 𝟙 M))) ≫
      derivedHomBaseChange.{uR, uA, uM} f F comparison K' M =
    derivedHomBaseChange.{uR, uA, uM} f F comparison K M ≫
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).map
        (show (op (F.obj K), F.obj M) ⟶ (op (F.obj K'), F.obj M) from ((F.map g).op, 𝟙 _)) := by
  intro F comparison _ K K' g M
  let adj := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
    f F comparison
  let μ := derivedHomBaseChangeMate.{uR, uA, uM} f F comparison
  simp only [derivedHomBaseChange]
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  rw [μ.naturality (show (op K, M) ⟶ (op K', M) from (g.op, 𝟙 M))]
  change μ.app (op K, M) ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map
      ((ScalarTransportedInternalHom.hom A).map
        ((F.op.prod F).map (show (op K, M) ⟶ (op K', M) from (g.op, 𝟙 M)))) = _
  congr 3
  exact Prod.ext rfl (F.map_id M)

end Stacks.DerivedHom.ExtensionOfScalars

namespace Stacks.LocalCohomology.LocalDualityTransfer

variable {A S : Type u} [CommRing A] [CommRing S] (f : A →+* S) (hf : f.Flat)

/-- The total derived extension of scalars along a flat map, as the functor induced on derived
categories by the exact functor `S ⊗_A -`. -/
abbrev flatDerived : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory

/-- **Flat base change of the cohomology of derived Hom, natural in the source.** For a flat
ring map `f : A → S`, a pseudo-coherent `K` and a bounded-below `ω`,
`S ⊗_A Hⁿ(RHom_A(K, ω)) ≅ Hⁿ(RHom_S(S ⊗ᴸ K, S ⊗ᴸ ω))`. -/
def extFlatBaseChangeIso (ω K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (hω : ∃ b : ℤ, ω.IsGE b) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (op K, ω))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} S).obj
          (op ((flatDerived f hf).obj K), (flatDerived f hf).obj ω)) := by
  let G := ModuleCat.extendScalars.{u, u, u} f
  letI : Limits.PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' f hf
  let F := G.mapDerivedCategory
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  letI : F.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F G.mapDerivedCategoryFactors
  letI : G.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj f).isRightAdjoint
  letI : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj f).isLeftAdjoint
  let t := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} f F
    G.mapDerivedCategoryFactors.hom K ω
  have ht : IsIso t := Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u}
    f F G.mapDerivedCategoryFactors.hom K ω (Or.inr (Or.inr (Or.inl ⟨hf, hK, hω⟩)))
  exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso G n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).mapIso (asIso t)

/-- The flat base change of `extFlatBaseChangeIso` is natural in the source. -/
theorem extFlatBaseChangeIso_naturality (ω : DerivedCategory (ModuleCat.{u} A))
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hK' : StacksDraft.PseudoCoherence.IsPseudoCoherent K') (hω : ∃ b : ℤ, ω.IsGE b) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} f).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).map
            (show (op K, ω) ⟶ (op K', ω) from (g.op, 𝟙 ω)))) ≫
      (extFlatBaseChangeIso f hf ω K' hK' hω n).hom =
    (extFlatBaseChangeIso f hf ω K hK hω n).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} S).map
          (show (op ((flatDerived f hf).obj K), (flatDerived f hf).obj ω) ⟶
              (op ((flatDerived f hf).obj K'), (flatDerived f hf).obj ω) from
            (((flatDerived f hf).map g).op, 𝟙 _))) := by
  let G := ModuleCat.extendScalars.{u, u, u} f
  let : Limits.PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' f hf
  let F := G.mapDerivedCategory
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let : F.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F G.mapDerivedCategoryFactors
  let : G.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  let : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj f).isRightAdjoint
  let : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj f).isLeftAdjoint
  have hnat :=
    Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality_left.{u, u, u} f F
      G.mapDerivedCategoryFactors.hom g ω
  have hH := ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso G n).inv.naturality
    ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).map
      (show (op K, ω) ⟶ (op K', ω) from (g.op, 𝟙 ω))))
  simp only [extFlatBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, asIso_hom, Category.assoc]
  dsimp only [Functor.comp_map] at hH
  rw [reassoc_of% hH, ← Functor.map_comp, ← Functor.map_comp, hnat]

end Stacks.LocalCohomology.LocalDualityTransfer
