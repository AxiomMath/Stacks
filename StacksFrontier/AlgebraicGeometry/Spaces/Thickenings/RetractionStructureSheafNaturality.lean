module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheafSquareZero
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison

/-!
# Naturality in `V` of the structure sheaf `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` of `X₀ ×_{Spec k} Spec k[V]`

Let `X₀ ⟶ X_V ⟶ X₀` be the base change of `Spec k ⟶ Spec k[V] ⟶ Spec k` along
`p : X₀ ⟶ Spec k`, so that the structure sheaf of `X_V` carried to the small étale site of `X₀`
is `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` (`AlgebraicGeometry.Space.squareZeroRetractionRingIso`). A linear map
`f : V ⟶ W` induces `Spec k[W] ⟶ Spec k[V]`, and a morphism `g : X_W ⟶ X_V` over it compatible
with the sections and the retractions induces the ring map `q_{V*} 𝒪_{X_V} ⟶ q_{W*} 𝒪_{X_W}`
of pullback of functions (`AlgebraicGeometry.Space.thickeningRetractionRingMap`). Under the two
identifications it is the map `𝒪_{X₀}[𝒪_{X₀} ⊗_k V] ⟶ 𝒪_{X₀}[𝒪_{X₀} ⊗_k W]` induced by
`𝒪_{X₀} ⊗_k f` (`AlgebraicGeometry.Space.squareZeroRetractionRingIso_naturality`), that is
`Deformation.ComplexLift.coefficientRingMap` for finite-dimensional `V`, `W`
(`AlgebraicGeometry.Space.squareZeroRetractionRingIso_naturality_coefficientRingMap`).

The proof goes through the three steps of the construction, each natural on its own:

* a split square-zero extension `A ≅ O₀[ker r]` is natural in maps of split extensions
  (`Deformation.ComplexLift.splitSqZeroExtIso_inv_naturality`);
* the gluing of a comparison `𝓕 ⊗_R M ⟶ G` is natural in `M` and `G`
  (`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfComparisonOfHom_naturality`);
* on the ideals, `g` carries `s(a) · j_V(v)` to `s(a) · j_W(f v)`
  (`AlgebraicGeometry.Space.retractionIdealIso_naturality`), since the functions `j(v) = (0, v)`
  of `Spec k[V]` pull back to `j(f v)` on `Spec k[W]`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

/- See `StacksFrontier/Deformation/ToposThickening/CoefficientSquareZeroReduction.lean`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

/-! ### Naturality of the gluing of a comparison -/

namespace Stacks.TensorByBaseModule

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C]
  (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.obj)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The comparison is natural**: for `f : M ⟶ N` and `ψ : G ⟶ G'` with `σ' (f m) = σ m ≫ ψ`,
the comparisons of `σ` and `σ'` commute with `𝓕 ⊗_R f` and `ψ`, at the level of presheaves. -/
theorem comparisonOfHom_naturality_of_compatible {M N : ModuleCat.{w} R} (f : M ⟶ N)
    {P P' : PMod O.obj}
    (ψ : P ⟶ P') (σ : M → (𝓕.val ⟶ P))
    (hadd : ∀ (m₁ m₂ : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ (m₁ + m₂)).app X).hom x = ((σ m₁).app X).hom x + ((σ m₂).app X).hom x)
    (hsmul : ∀ (r : R) (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ m).app X).hom x)
    (σ' : N → (𝓕.val ⟶ P'))
    (hadd' : ∀ (m₁ m₂ : N) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (m₁ + m₂)).app X).hom x = ((σ' m₁).app X).hom x + ((σ' m₂).app X).hom x)
    (hsmul' : ∀ (r : R) (m : N) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ' m).app X).hom x)
    (hσ : ∀ (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (f m)).app X).hom x = (ψ.app X).hom (((σ m).app X).hom x)) :
    (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map f ≫
        comparison R J O 𝓕 θ N P' σ' hadd' hsmul' =
      comparison R J O 𝓕 θ M P σ hadd hsmul ≫ ψ := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  let := coefficientAlgebraOfHom R J O θ X
  suffices h :
      ((comparisonApp R J O 𝓕 θ N P' σ' hadd' hsmul' X).hom.toAddMonoidHom.comp
          (((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map f).app X).hom.toAddMonoidHom :
        (𝓕.val.obj X ⊗[O.obj.obj X] (O.obj.obj X ⊗[R] M)) →+ P'.obj X)
        = (ψ.app X).hom.toAddMonoidHom.comp
          (comparisonApp R J O 𝓕 θ M P σ hadd hsmul X).hom.toAddMonoidHom by
    exact congrFun (congrArg DFunLike.coe h) t
  refine addHom_ext_tmul_tmul fun x a m => ?_
  show (comparisonApp R J O 𝓕 θ N P' σ' hadd' hsmul' X).hom
      ((((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map f).app X).hom
        ((x ⊗ₜ[O.obj.obj X] (a ⊗ₜ[R] m) :
          𝓕.val.obj X ⊗[O.obj.obj X] (O.obj.obj X ⊗[R] M)))) =
    (ψ.app X).hom (a • ((σ m).app X).hom x)
  rw [(ψ.app X).hom.map_smul, ← hσ]
  rfl

/-- **The gluing of a comparison is natural**: for `f : M ⟶ N` and `ψ : G ⟶ G'` with
`σ' (f m) = σ m ≫ ψ`, the isomorphisms `𝓕 ⊗_R M ≅ G` and `𝓕 ⊗_R N ≅ G'` of
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfComparisonOfHom` commute with `𝓕 ⊗_R f` and
`ψ`. -/
theorem tensorByBaseModuleIsoOfComparisonOfHom_naturality {M N : ModuleCat.{w} R} (f : M ⟶ N)
    {G G' : SheafOfModules.{w} (ringSheaf J O)} (ψ : G ⟶ G')
    (σ : M → (𝓕.val ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
      ((SheafOfModules.forget (ringSheaf J O)).obj G)))
    (hadd : ∀ (m₁ m₂ : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ (m₁ + m₂)).app X).hom x = ((σ m₁).app X).hom x + ((σ m₂).app X).hom x)
    (hsmul : ∀ (r : R) (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ m).app X).hom x)
    (σ' : N → (𝓕.val ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
      ((SheafOfModules.forget (ringSheaf J O)).obj G')))
    (hadd' : ∀ (m₁ m₂ : N) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (m₁ + m₂)).app X).hom x = ((σ' m₁).app X).hom x + ((σ' m₂).app X).hom x)
    (hsmul' : ∀ (r : R) (m : N) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ' m).app X).hom x)
    (P : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)
    (hbij : ∀ W : C, P W →
      Function.Bijective (comparisonApp R J O 𝓕 θ M _ σ hadd hsmul (op W)).hom)
    (hbij' : ∀ W : C, P W →
      Function.Bijective (comparisonApp R J O 𝓕 θ N _ σ' hadd' hsmul' (op W)).hom)
    (hσ : ∀ (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
      ((σ' (f m)).app X).hom x = (ψ.val.app X).hom (((σ m).app X).hom x)) :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).map f ≫
        (tensorByBaseModuleIsoOfComparisonOfHom R J O 𝓕 θ N G' σ' hadd' hsmul' P hcov
          hbij').hom =
      (tensorByBaseModuleIsoOfComparisonOfHom R J O 𝓕 θ M G σ hadd hsmul P hcov hbij).hom ≫
        ψ := by
  have hp := comparisonOfHom_naturality_of_compatible R J O 𝓕 θ f
    ((PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map
      ((SheafOfModules.forget (ringSheaf J O)).map ψ)) σ hadd hsmul σ' hadd' hsmul' hσ
  let adj := PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 (ringSheaf J O).obj)
  have h1 := adj.homEquiv_naturality_left_symm
    ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map f)
    (comparison R J O 𝓕 θ N _ σ' hadd' hsmul')
  have h2 := adj.homEquiv_naturality_right_symm
    (comparison R J O 𝓕 θ M _ σ hadd hsmul) ψ
  have k : ∀ {Q : PMod O.obj} {H : SheafOfModules.{w} (ringSheaf J O)}
      (Φ : Q ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj H)),
      (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ =
        (adj.homEquiv Q H).symm Φ := fun {Q H} Φ => (adj.homEquiv Q H).injective (by
    rw [Equiv.apply_symm_apply, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
      Equiv.apply_symm_apply])
  have e1 : (tensorByBaseModuleIsoOfComparisonOfHom R J O 𝓕 θ N G' σ' hadd' hsmul' P hcov
      hbij').hom = (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm
        (comparison R J O 𝓕 θ N _ σ' hadd' hsmul') := rfl
  have e2 : (tensorByBaseModuleIsoOfComparisonOfHom R J O 𝓕 θ M G σ hadd hsmul P hcov
      hbij).hom = (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm
        (comparison R J O 𝓕 θ M _ σ hadd hsmul) := rfl
  rw [e1, e2, k, k]
  exact h1.symm.trans ((congrArg (adj.homEquiv _ _).symm hp).trans h2)

end Stacks.TensorByBaseModule

/-! ### Naturality of the trivialization of a split square-zero extension -/

namespace Deformation.ComplexLift

open PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ A A' : Sheaf J CommRingCat.{u}} {s : O₀ ⟶ A} {r : A ⟶ O₀} {s' : O₀ ⟶ A'}
  {r' : A' ⟶ O₀} (G : A ⟶ A') (hGs : s ≫ G = s') (hGr : G ≫ r' = r)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
include hGs in
/-- `G` carries `s(a) · x` to `s'(a) · G x`. -/
theorem splitIdealMap_smul_aux (U : Cᵒᵖ) (a : O₀.obj.obj U) (x : A.obj.obj U) :
    G.hom.app U (s.hom.app U a * x) = s'.hom.app U a * G.hom.app U x := by
  rw [map_mul, ← hGs]
  rfl

include hGr in
/-- `G` carries the kernel of `r` into the kernel of `r'`. -/
theorem splitIdealMap_mem_aux {U : Cᵒᵖ} (m : (splitIdeal s r).val.obj U) :
    r'.hom.app U (G.hom.app U (splitIdealVal s r m)) = 0 :=
  (congrArg (fun φ : A ⟶ O₀ => φ.hom.app U (splitIdealVal s r m)) hGr).trans
    (splitIdealVal_mem s r m)

/-- **The map of kernels induced by a map of split extensions**: `G : A ⟶ A'` with `s ≫ G = s'`
and `G ≫ r' = r` carries the kernel of `r` into the kernel of `r'`, `O₀`-linearly. -/
def splitIdealMap : splitIdeal s r ⟶ splitIdeal s' r' :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m => splitIdealMk s' r' (G.hom.app U (splitIdealVal s r m))
          (splitIdealMap_mem_aux G hGr m))
        (fun m n => splitIdealVal_injective s' r' (map_add (G.hom.app U).hom _ _)))
      naturality {U V} i := by
        ext m
        refine splitIdealVal_injective s' r' ?_
        change G.hom.app V (A.obj.map i (splitIdealVal s r m)) =
          A'.obj.map i (G.hom.app U (splitIdealVal s r m))
        rw [← CommRingCat.comp_apply, G.hom.naturality, CommRingCat.comp_apply] }
    (fun U a m => splitIdealVal_injective s' r' (splitIdealMap_smul_aux G hGs U a _))⟩

/-- The map of kernels is `G` on the underlying sections. -/
theorem splitIdealVal_splitIdealMap {U : Cᵒᵖ} (m : (splitIdeal s r).val.obj U) :
    splitIdealVal s' r' ((splitIdealMap G hGs hGr).val.app U m) =
      G.hom.app U (splitIdealVal s r m) := rfl

variable (hsq : ∀ (U : Cᵒᵖ) (a b : A.obj.obj U), r.hom.app U a = 0 → r.hom.app U b = 0 → a * b = 0)
  (hsq' : ∀ (U : Cᵒᵖ) (a b : A'.obj.obj U), r'.hom.app U a = 0 → r'.hom.app U b = 0 → a * b = 0)

/-- **`O₀[ker r] ⟶ A` is natural in maps of split extensions**: `(a, m) ↦ s(a) + m` followed by
`G` is `(a, m) ↦ (a, G m)` followed by `(a, m') ↦ s'(a) + m'`. -/
theorem splitSqZeroExtHom_naturality :
    splitSqZeroExtHom s r hsq ≫ G =
      sqZeroExtSheafAnySiteMap (splitIdealMap G hGs hGr) ≫ splitSqZeroExtHom s' r' hsq' := by
  ext U x
  show G.hom.app U (s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
      splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)) =
    s'.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
      G.hom.app U (splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x))
  rw [map_add, ← hGs]
  rfl

variable (hsr : s ≫ r = 𝟙 O₀) (hsr' : s' ≫ r' = 𝟙 O₀)

/-- **`A ≅ O₀[ker r]` is natural in maps of split extensions.** -/
theorem splitSqZeroExtIso_inv_naturality :
    G ≫ (splitSqZeroExtIso s' r' hsr' hsq').inv =
      (splitSqZeroExtIso s r hsr hsq).inv ≫ sqZeroExtSheafAnySiteMap (splitIdealMap G hGs hGr) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact splitSqZeroExtHom_naturality G hGs hGr hsq hsq'

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Two isomorphisms of sheaves of modules intertwining `φ` and `ψ` induce, on the trivial
square-zero extensions, inverses intertwining `ψ` and `φ`. -/
theorem sqZeroExtSheafAnySiteMap_inv_naturality
    {M M' N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (e : M ≅ M') (e' : N ≅ N') (φ : M ⟶ N) (ψ : M' ⟶ N') (hφψ : φ ≫ e'.hom = e.hom ≫ ψ) :
    sqZeroExtSheafAnySiteMap ψ ≫ sqZeroExtSheafAnySiteMap e'.inv =
      sqZeroExtSheafAnySiteMap e.inv ≫ sqZeroExtSheafAnySiteMap φ := by
  rw [← sqZeroExtSheafAnySiteMap_comp, ← sqZeroExtSheafAnySiteMap_comp]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, hφψ, Iso.inv_hom_id_assoc]

end Deformation.ComplexLift

/-! ### The ring map of a morphism of retractions -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X'V X'W : AlgebraicSpaces B S hS}
  {qV : X'V ⟶ X} (hqV : yoneda.relativelyRepresentable qV.hom)
  {qW : X'W ⟶ X} (hqW : yoneda.relativelyRepresentable qW.hom)
  {g : X'W ⟶ X'V} (hg : g ≫ qV = qW)

include hg in
/-- `g ≫ q_V = q_W` on the underlying morphisms of presheaves. -/
theorem retractionMap_hom_comp : g.hom ≫ qV.hom = qW.hom :=
  congrArg (fun t : X'W ⟶ X => t.hom) hg

/-- **The map of base-changed charts** `U ×_X X'_W ⟶ U ×_X X'_V` induced by `g : X'_W ⟶ X'_V`
over `X`. -/
def thickeningRetractionChartMap (U : SmallEtale B S hS X.1) :
    hqW.pullback U.1.hom ⟶ hqV.pullback U.1.hom :=
  hqV.lift (hqW.fst U.1.hom ≫ g.hom) (hqW.snd U.1.hom) (by
    rw [Category.assoc, retractionMap_hom_comp B S hS hg]
    exact hqW.w U.1.hom)

/-- The map of base-changed charts lies over `g`. -/
theorem thickeningRetractionChartMap_fst (U : SmallEtale B S hS X.1) :
    yoneda.map (thickeningRetractionChartMap B S hS hqV hqW hg U) ≫ hqV.fst U.1.hom =
      hqW.fst U.1.hom ≫ g.hom :=
  hqV.lift_fst _ _ _

/-- The map of base-changed charts lies over `U`. -/
theorem thickeningRetractionChartMap_snd (U : SmallEtale B S hS X.1) :
    thickeningRetractionChartMap B S hS hqV hqW hg U ≫ hqV.snd U.1.hom = hqW.snd U.1.hom :=
  hqV.lift_snd _ _ _

/-- **The map of base-changed charts is the unique map over `U` and over `g`.** -/
theorem eq_thickeningRetractionChartMap (U : SmallEtale B S hS X.1)
    (m : hqW.pullback U.1.hom ⟶ hqV.pullback U.1.hom)
    (hfst : yoneda.map m ≫ hqV.fst U.1.hom = hqW.fst U.1.hom ≫ g.hom)
    (hsnd : m ≫ hqV.snd U.1.hom = hqW.snd U.1.hom) :
    m = thickeningRetractionChartMap B S hS hqV hqW hg U :=
  hqV.hom_ext (hfst.trans (thickeningRetractionChartMap_fst B S hS hqV hqW hg U).symm)
    (hsnd.trans (thickeningRetractionChartMap_snd B S hS hqV hqW hg U).symm)

/-- The maps of base-changed charts are natural in the chart. -/
def thickeningRetractionChartTrans :
    smallBaseChange B S hS qW hqW ⋙ SmallEtale.toOver B S hS X'W.1 ⟶
      smallBaseChange B S hS qV hqV ⋙ SmallEtale.toOver B S hS X'V.1 where
  app U := thickeningRetractionChartMap B S hS hqV hqW hg U
  naturality {U U'} k := by
    have key : hqW.lift (hqW.fst U.1.hom) (hqW.snd U.1.hom ≫ k.hom.left)
          (representablePullback_lift_cond B S hS qW hqW k) ≫
          thickeningRetractionChartMap B S hS hqV hqW hg U' =
        thickeningRetractionChartMap B S hS hqV hqW hg U ≫
          hqV.lift (hqV.fst U.1.hom) (hqV.snd U.1.hom ≫ k.hom.left)
            (representablePullback_lift_cond B S hS qV hqV k) :=
      hqV.hom_ext (by simp [thickeningRetractionChartMap]) (by simp [thickeningRetractionChartMap])
    exact key

/-- **The ring map `q_{V*} 𝒪_{X'_V} ⟶ q_{W*} 𝒪_{X'_W}` of a morphism `g : X'_W ⟶ X'_V` over
`X`**: pullback of functions along the maps `U ×_X X'_W ⟶ U ×_X X'_V` of base-changed charts. -/
def thickeningRetractionRingMap :
    thickeningRetractionRing B S hS hqV ⟶ thickeningRetractionRing B S hS hqW where
  hom := Functor.whiskerRight (NatTrans.op (thickeningRetractionChartTrans B S hS hqV hqW hg))
    ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ)

/-- The ring map over a chart is pullback along the map of base-changed charts. -/
theorem thickeningRetractionRingMap_app_apply (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (thickeningRetractionRing B S hS hqV).obj.obj U) :
    (thickeningRetractionRingMap B S hS hqV hqW hg).hom.app U x =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (thickeningRetractionChartMap B S hS hqV hqW hg U.unop)).op x := rfl

/-- Pullback of regular functions along `a` and `b` is pullback along `c` when `a ≫ b = c`. -/
private theorem Γ_map_toScheme_comp_apply_of_eq {Y Z T : BigFppfOver B S hS} {a : Y ⟶ Z}
    {b : Z ⟶ T} {c : Y ⟶ T} (h : a ≫ b = c) (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op).hom x) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c).op).hom x :=
  h ▸ (Γ_map_toScheme_comp_apply B S hS a b x).symm

/-- **`g` commutes with the sections**: `𝒪_X ⟶ q_{V*} 𝒪_{X'_V} ⟶ q_{W*} 𝒪_{X'_W}` is the
section of `X'_W`, the charts maps commuting with the projections to `U`. -/
theorem thickeningRetractionSection_comp_ringMap :
    thickeningRetractionSection B S hS hqV ≫ thickeningRetractionRingMap B S hS hqV hqW hg =
      thickeningRetractionSection B S hS hqW := by
  ext U x
  exact Γ_map_toScheme_comp_apply_of_eq B S hS
    (thickeningRetractionChartMap_snd B S hS hqV hqW hg U.unop) x

/-- **`g` commutes with pulled-back functions of the bases**: for `e : T_W ⟶ T_V` with
`g ≫ p'_V = p'_W ≫ e`, pulling a function of `T_V` back to `U ×_X X'_V` and then along `g` is
pulling its image in `Γ(T_W)` back to `U ×_X X'_W`. -/
theorem thickeningRetractionRingMap_baseFunction {TV TW : BigFppfOver B S hS} {e : TW ⟶ TV}
    {p'V : X'V.1 ⟶ yoneda.obj TV} {p'W : X'W.1 ⟶ yoneda.obj TW}
    (hgp : g.hom ≫ p'V = p'W ≫ yoneda.map e) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj TV))) :
    (thickeningRetractionRingMap B S hS hqV hqW hg).hom.app U
        (retractionBaseFunction B S hS hqV (p' := p'V) U.unop t) =
      retractionBaseFunction B S hS hqW (p' := p'W) U.unop
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map e).op t) := by
  have hm : thickeningRetractionChartMap B S hS hqV hqW hg U.unop ≫
      retractionChartToBase B S hS hqV (p' := p'V) U.unop =
        retractionChartToBase B S hS hqW (p' := p'W) U.unop ≫ e := by
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    show yoneda.map (thickeningRetractionChartMap B S hS hqV hqW hg U.unop) ≫
        yoneda.map (Yoneda.fullyFaithful.preimage (hqV.fst U.unop.1.hom ≫ p'V)) =
      yoneda.map (Yoneda.fullyFaithful.preimage (hqW.fst U.unop.1.hom ≫ p'W)) ≫ yoneda.map e
    rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
      ← Category.assoc, thickeningRetractionChartMap_fst, Category.assoc, hgp, Category.assoc]
  exact (Γ_map_toScheme_comp_apply_of_eq B S hS hm t).trans
    (Γ_map_toScheme_comp_apply B S hS _ _ t)

section Restriction

variable {iV : X ⟶ X'V} (hiV : IsThickeningHom B S hS iV) (hV : iV ≫ qV = 𝟙 X)
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW) (hW : iW ≫ qW = 𝟙 X)

variable {B S hS} in
/-- The section `U ⟶ U ×_X X'` of a chart, through `X ⟶ X'`. -/
def retractionSectionChart {X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {q : X' ⟶ X}
    (h : i ≫ q = 𝟙 X) (hq : yoneda.relativelyRepresentable q.hom) (U : SmallEtale B S hS X.1) :
    U.1.left ⟶ hq.pullback U.1.hom :=
  hq.lift (U.1.hom ≫ i.hom) (𝟙 U.1.left) (by
    rw [Category.assoc, retraction_hom_comp B S hS i q h, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.id_comp])

variable {B S hS} in
/-- **Restriction to `X` on a base-changed chart** is pullback along the section
`U ⟶ U ×_X X'`. -/
theorem thickeningRetractionRestriction_app_apply {X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) {q : X' ⟶ X} (h : i ≫ q = 𝟙 X)
    (hq : yoneda.relativelyRepresentable q.hom) (U : SmallEtale B S hS X.1)
    (x : (thickeningRetractionRing B S hS hq).obj.obj (op U)) :
    (thickeningRetractionRestriction B S hS hi h hq).hom.app (op U) x =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (retractionSectionChart h hq U)).op x :=
  Γ_map_toScheme_comp_apply_of_eq B S hS
    (a := ((smallBaseChangeRetractionIso B S hS i q h hi.isClosedImmersion.rep hq).inv.app
      U).hom.left)
    (hi.isClosedImmersion.rep.lift_snd _ _ _) x

include hV in
/-- The sections `U ⟶ U ×_X X'` commute with the map of base-changed charts, as
`i_W ≫ g = i_V`. -/
theorem retractionSectionChart_comp_chartMap (hig : iW ≫ g = iV) (U : SmallEtale B S hS X.1) :
    retractionSectionChart hW hqW U ≫ thickeningRetractionChartMap B S hS hqV hqW hg U =
      retractionSectionChart hV hqV U := by
  have hig' : iW.hom ≫ g.hom = iV.hom := congrArg (fun t : X ⟶ X'V => t.hom) hig
  refine hqV.hom_ext ?_ ?_
  · simp [retractionSectionChart, thickeningRetractionChartMap, hig']
  · simp [retractionSectionChart, thickeningRetractionChartMap]

include hV in
/-- **`g` commutes with the restrictions to `X`**, as `i_W ≫ g = i_V`. -/
theorem thickeningRetractionRingMap_comp_restriction (hig : iW ≫ g = iV) :
    thickeningRetractionRingMap B S hS hqV hqW hg ≫
        thickeningRetractionRestriction B S hS hiW hW hqW =
      thickeningRetractionRestriction B S hS hiV hV hqV := by
  ext U x
  refine (thickeningRetractionRestriction_app_apply hiW hW hqW U.unop _).trans ?_
  refine Eq.trans ?_ (thickeningRetractionRestriction_app_apply hiV hV hqV U.unop x).symm
  exact Γ_map_toScheme_comp_apply_of_eq B S hS
    (retractionSectionChart_comp_chartMap B S hS hqV hqW hg hV hW hig U.unop) x

/-! ### The identifications are natural -/

section Naturality

open Deformation.ComplexLift Stacks.TensorByBaseModule

variable (hig : iW ≫ g = iV)
  {T₀ TV TW : BigFppfOver B S hS} {τV : TV ⟶ T₀} {βV : T₀ ⟶ TV} {τW : TW ⟶ T₀} {βW : T₀ ⟶ TW}
  {e : TW ⟶ TV} {p : X.1 ⟶ yoneda.obj T₀} {p'V : X'V.1 ⟶ yoneda.obj TV}
  {p'W : X'W.1 ⟶ yoneda.obj TW} (hgp : g.hom ≫ p'V = p'W ≫ yoneda.map e)
  (hipV : iV.hom ≫ p'V = p ≫ yoneda.map βV) (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : βV ≫ τV = 𝟙 T₀)
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map βW) (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : βW ≫ τW = 𝟙 T₀)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj TV)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj TW)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
  (R : Type u) [CommRing R]
  (φ₀ : CommRingCat.of R ≅ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀)))
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (jV : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj TV)))
  (hjβV : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map βV).op (jV m) = 0)
  (hjsV : ∀ (c : R) (m : M), jV (c • m) =
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τV).op (φ₀.hom c) * jV m)
  (hjinjV : Function.Injective jV)
  (hjkerV : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map βV).op t = 0 → ∃ m, jV m = t)
  (hjsqV : ∀ m m', jV m * jV m' = 0)
  (jW : N →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj TW)))
  (hjβW : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map βW).op (jW m) = 0)
  (hjsW : ∀ (c : R) (m : N), jW (c • m) =
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τW).op (φ₀.hom c) * jW m)
  (hjinjW : Function.Injective jW)
  (hjkerW : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map βW).op t = 0 → ∃ m, jW m = t)
  (hjsqW : ∀ m m', jW m * jW m' = 0)
  (f : M →ₗ[R] N)
  (hje : ∀ m, jW (f m) = Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map e).op (jV m))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj TV)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj TW)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)] in
include hig hgp hje in
/-- **On the comparison families, `g` is `f`**: `g` carries `s(a) · j_V(m)` to
`s(a) · j_W(f m)`. -/
theorem retractionComparisonFamily_naturality (m : M) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val.obj U) :
    ((retractionComparisonFamily B S hS hiW hW hqW hipW R jW hjβW (f m)).app U).hom x =
      ((splitIdealMap (thickeningRetractionRingMap B S hS hqV hqW hg)
          (thickeningRetractionSection_comp_ringMap B S hS hqV hqW hg)
          (thickeningRetractionRingMap_comp_restriction B S hS hqV hqW hg hiV hV hiW hW
            hig)).val.app
        U).hom (((retractionComparisonFamily B S hS hiV hV hqV hipV R jV hjβV m).app U).hom x) := by
  apply splitIdealVal_injective (thickeningRetractionSection B S hS hqW)
    (thickeningRetractionRestriction B S hS hiW hW hqW)
  show (thickeningRetractionSection B S hS hqW).hom.app U
      (show (structureSheaf B S hS X.1 X.2).obj.obj U from x) *
        retractionBaseFunction B S hS hqW (p' := p'W) U.unop (jW (f m)) =
    (thickeningRetractionRingMap B S hS hqV hqW hg).hom.app U
      ((thickeningRetractionSection B S hS hqV).hom.app U
        (show (structureSheaf B S hS X.1 X.2).obj.obj U from x) *
        retractionBaseFunction B S hS hqV (p' := p'V) U.unop (jV m))
  rw [map_mul, thickeningRetractionRingMap_baseFunction B S hS hqV hqW hg hgp U, hje]
  congr 1
  exact (congrArg (fun φ => φ.hom.app U (show (structureSheaf B S hS X.1 X.2).obj.obj U from x))
    (thickeningRetractionSection_comp_ringMap B S hS hqV hqW hg)).symm

include hig hgp hje in
/-- **The identification `𝒪_X ⊗_R M ≅ ker r` of the ideal is natural**: under the
identifications for `X'_V` and `X'_W`, the map of ideals induced by `g` is `𝒪_X ⊗_R f`. -/
theorem retractionIdealIso_naturality :
    (tensorByBaseModuleOfHom R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (retractionCoefficientMap B S hS (p := p) R φ₀.hom)).map
        (ModuleCat.ofHom f) ≫
      (retractionIdealIso hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW).hom =
    (retractionIdealIso hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV).hom ≫
      splitIdealMap (thickeningRetractionRingMap B S hS hqV hqW hg)
        (thickeningRetractionSection_comp_ringMap B S hS hqV hqW hg)
        (thickeningRetractionRingMap_comp_restriction B S hS hqV hqW hg hiV hV hiW hW hig) :=
  tensorByBaseModuleIsoOfComparisonOfHom_naturality R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
    (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (ModuleCat.ofHom f) _ _
    (retractionComparisonFamily_add B S hS hiV hV hqV hipV R jV hjβV)
    (retractionComparisonFamily_smul B S hS hiV hV hqV hipV jV hjβV hpbV hjsV) _
    (retractionComparisonFamily_add B S hS hiW hW hqW hipW R jW hjβW)
    (retractionComparisonFamily_smul B S hS hiW hW hqW hipW jW hjβW hpbW hjsW) _
    (generate_isAffine_chart_mem B S hS X)
    (fun U hU => (bijective_comparisonApp_iff R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (ModuleCat.of R M) _ _ _ _ (op U)).mpr
      (bijective_retractionComparison hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV U hU))
    (fun U hU => (bijective_comparisonApp_iff R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (ModuleCat.of R N) _ _ _ _ (op U)).mpr
      (bijective_retractionComparison hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW U hU))
    (retractionComparisonFamily_naturality B S hS hqV hqW hg hiV hV hiW hW hig hgp hipV hipW R
      jV hjβV jW hjβW f hje)

include hig hgp hje in
/-- **The identification `q_* 𝒪_{X'} ≅ 𝒪_X[𝒪_X ⊗_R M]` is natural**: under the identifications for
`X'_V` and `X'_W`, the ring map `q_{V*} 𝒪_{X'_V} ⟶ q_{W*} 𝒪_{X'_W}` of `g` is the map
`𝒪_X[𝒪_X ⊗_R M] ⟶ 𝒪_X[𝒪_X ⊗_R N]` induced by `𝒪_X ⊗_R f`. -/
theorem thickeningRetractionRingIso_naturality :
    thickeningRetractionRingMap B S hS hqV hqW hg ≫
        (thickeningRetractionRingIso hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW hjsqW).hom =
      (thickeningRetractionRingIso hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV hjsqV).hom ≫
        sqZeroExtSheafAnySiteMap
          ((tensorByBaseModuleOfHom R (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (retractionCoefficientMap B S hS (p := p) R φ₀.hom)).map (ModuleCat.ofHom f)) := by
  have hI := retractionIdealIso_naturality B S hS hqV hqW hg hiV hV hiW hW hig hgp hipV hpbV hβτV
    hipW hpbW hβτW R φ₀ jV hjβV hjsV hjinjV hjkerV jW hjβW hjsW hjinjW hjkerW f hje
  have hspl := splitSqZeroExtIso_inv_naturality (thickeningRetractionRingMap B S hS hqV hqW hg)
    (thickeningRetractionSection_comp_ringMap B S hS hqV hqW hg)
    (thickeningRetractionRingMap_comp_restriction B S hS hqV hqW hg hiV hV hiW hW hig)
    (thickeningRetraction_mul_eq_zero hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV hjsqV)
    (thickeningRetraction_mul_eq_zero hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW hjsqW)
    (thickeningRetractionSection_comp_restriction B S hS hiV hV hqV)
    (thickeningRetractionSection_comp_restriction B S hS hiW hW hqW)
  refine (congrArg (thickeningRetractionRingMap B S hS hqV hqW hg ≫ ·)
    (show (thickeningRetractionRingIso hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW
      hjsqW).hom = _ ≫ sqZeroExtSheafAnySiteMap
        (retractionIdealIso hiW hW hipW hpbW hβτW jW hjβW hjsW hjinjW hjkerW).inv
      from rfl)).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _)
    (show (thickeningRetractionRingIso hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV
      hjsqV).hom = _ ≫ sqZeroExtSheafAnySiteMap
        (retractionIdealIso hiV hV hipV hpbV hβτV jV hjβV hjsV hjinjV hjkerV).inv from rfl)).symm
  rw [Iso.symm_hom, Iso.symm_hom, ← Category.assoc, hspl, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (sqZeroExtSheafAnySiteMap_inv_naturality _ _ _ _ hI)

end Naturality

/-! ### The base change of `Spec k ⟶ Spec k[V] ⟶ Spec k` -/

section SquareZero

open Deformation.Artin Deformation.ComplexLift Stacks.TensorByBaseModule

variable (k : Type u) [CommRing k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))

/-- **The functions `(0, v)` of `Spec k[V]` are natural in `V`**: `Spec k[W] ⟶ Spec k[V]` pulls
`(0, v)` back to `(0, f v)`. -/
theorem dualNumbersIdealInclusion_naturality {V W : SiteModule k B} (f : V ⟶ W) (v : V.obj) :
    dualNumbersIdealInclusion k B S hS toS W (f.hom v) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (squareZeroOverMap k B S hS toS f)).op
        (dualNumbersIdealInclusion k B S hS toS V v) := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ (TrivSqZeroExt.inr v))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom))
  refine Eq.trans ?_ h
  rw [dualNumbersIdealInclusion_apply]
  exact congrArg (squareZeroSectionsEquiv k B S hS toS W) (TrivSqZeroExt.map_inr f.hom.hom v).symm

variable {k B S hS toS hk} {V W : SiteModule k B} (f : V ⟶ W)
  (p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk))
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}

include hV hW in
/-- **The structure sheaf `𝒪_X[𝒪_X ⊗_k V]` of the base change `X'_V` of `Spec k[V]` is natural in
`V`** (Stacks 0DLL): for a linear map `f : V ⟶ W` and a morphism `g : X'_W ⟶ X'_V` over `X` and
over `Spec k[W] ⟶ Spec k[V]`, compatible with the sections, the identifications
`q_* 𝒪_{X'} ≅ 𝒪_X[𝒪_X ⊗_k -]` carry the pullback of functions along `g` to the map induced by
`𝒪_X ⊗_k f`. -/
theorem squareZeroRetractionRingIso_naturality
    (hipV : iV.hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
    (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
    (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
    (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
    (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
    (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
    (hig : iW ≫ g = iV)
    (hgp : g.hom ≫ p'V = p'W ≫ yoneda.map (squareZeroOverMap k B S hS toS f)) :
    (squareZeroRetractionRingIso hiV hV hipV hpbV hβτV).hom ≫
        sqZeroExtSheafAnySiteMap
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom) =
      thickeningRetractionRingMap B S hS hqV hqW hg ≫
        (squareZeroRetractionRingIso hiW hW hipW hpbW hβτW).hom :=
  (thickeningRetractionRingIso_naturality B S hS hqV hqW (hg := hg) (hiV := hiV) (hV := hV)
    (hiW := hiW) (hW := hW) (hig := hig) (hgp := hgp) (hipV := hipV) (hpbV := hpbV)
    (hβτV := hβτV) (hipW := hipW) (hpbW := hpbW) (hβτW := hβτW) (R := k)
    (φ₀ := squareZeroBaseIso k B S hS toS hk)
    (jV := dualNumbersIdealInclusion k B S hS toS V)
    (hjβV := dualNumbersIdealInclusion_retraction k B S hS toS hk V)
    (hjsV := dualNumbersIdealInclusion_smul hβτV)
    (hjinjV := dualNumbersIdealInclusion_injective k B S hS toS V)
    (hjkerV := dualNumbersIdealInclusion_surjective_ker k B S hS toS hk V)
    (hjsqV := dualNumbersIdealInclusion_mul k B S hS toS V)
    (jW := dualNumbersIdealInclusion k B S hS toS W)
    (hjβW := dualNumbersIdealInclusion_retraction k B S hS toS hk W)
    (hjsW := dualNumbersIdealInclusion_smul hβτW)
    (hjinjW := dualNumbersIdealInclusion_injective k B S hS toS W)
    (hjkerW := dualNumbersIdealInclusion_surjective_ker k B S hS toS hk W)
    (hjsqW := dualNumbersIdealInclusion_mul k B S hS toS W) (f := f.hom.hom)
    (hje := dualNumbersIdealInclusion_naturality B S hS k toS f)).symm

section Field

variable {k : Type u} [Field k] {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))}
  {V W : FGModuleCat.{u} k} (f : V ⟶ W) (p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk))
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V))}
  {τV : squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V) ⟶ algebraOver k B S hS toS hk}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS ((fgSiteModule B hk).obj W))}
  {τW : squareZeroOver k B S hS toS ((fgSiteModule B hk).obj W) ⟶ algebraOver k B S hS toS hk}

include hV hW in
/-- **`squareZeroRetractionRingIso_naturality` for finite-dimensional `V`, `W`**: the map induced
by `𝒪_X ⊗_k f` is `Deformation.ComplexLift.coefficientRingMap` of the `k`-algebra structure of
`𝒪_X` through `p`. -/
theorem squareZeroRetractionRingIso_naturality_coefficientRingMap
    (hipV : iV.hom ≫ p'V =
      p ≫ yoneda.map (squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)))
    (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
    (hβτV : squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V) ≫ τV = 𝟙 _)
    (hipW : iW.hom ≫ p'W =
      p ≫ yoneda.map (squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj W)))
    (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
    (hβτW : squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj W) ≫ τW = 𝟙 _)
    (hig : iW ≫ g = iV)
    (hgp : g.hom ≫ p'V =
      p'W ≫ yoneda.map (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f))) :
    (squareZeroRetractionRingIso hiV hV hipV hpbV hβτV).hom ≫
        coefficientRingMap (squareZeroCoefficientMap k B S hS toS hk p) f =
      thickeningRetractionRingMap B S hS hqV hqW hg ≫
        (squareZeroRetractionRingIso hiW hW hipW hpbW hβτW).hom :=
  squareZeroRetractionRingIso_naturality (hqV := hqV) (hqW := hqW) (hg := hg) (hiV := hiV)
    (hV := hV) (hiW := hiW) (hW := hW) (f := (fgSiteModule B hk).map f) (p := p) hipV hpbV hβτV
    hipW hpbW hβτW hig hgp

end Field

end SquareZero

end Restriction

end AlgebraicGeometry.Space

end
