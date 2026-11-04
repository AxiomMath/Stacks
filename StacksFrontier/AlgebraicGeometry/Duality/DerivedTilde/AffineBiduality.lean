module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineBidualityBounded
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHomBoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle
public import StacksFrontier.RingTheory.Ext.DerivedHomFiniteness

/-!
# Biduality for a complex with coherent cohomology on an affine Noetherian scheme

Let `R` be a Noetherian ring, `ω` a dualizing complex for `R` and `L` an object of `D(R)` with
finite cohomology modules, with no boundedness assumption. On `X = Spec R` the biduality morphism
of [Stacks, Tag 0A89]

`L̃ ⟶ R𝓗om(R𝓗om(L̃, ω̃), ω̃)`

is an isomorphism.

Write `D = R𝓗om(-, ω̃)` and let `ω` have injective amplitude in `[a, b]`. The degree-`i`
cohomology of the biduality morphism of `L̃` is that of `τ_{≥ m} τ_{≤ n} L`, for
`n ≥ i + (b - a)` and `m ≤ i - (b - a)`, where the bounded case applies. Indeed `D` carries
`D^{≥ k}_QCoh` into `D^{≤ b - k}` (`isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude`) and
`D^{≤ k}` into `D^{≥ a - k}` (`Stacks.SheafOfModules.isGE_derivedSheafHom`), it transforms
distinguished triangles into distinguished triangles ([Stacks, Tag 08I0]), and the biduality
morphism is natural; so the truncation triangles do not change the degree-`i` cohomology of
either side.

## Main results

* `Stacks.Duality.isIso_derivedBiduality_derivedTilde`: the biduality morphism of `ω̃`, `L̃` on
  `Spec R` is an isomorphism.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite TopologicalSpace
  AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace Stacks.Duality

open Stacks.SheafOfModules

variable (R : CommRingCat.{u})

section Main

variable [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-- **Biduality for a complex with finite cohomology on an affine scheme.** For `R` Noetherian,
`ω` a dualizing complex for `R` and `L` an object of `D(R)` all of whose cohomology modules are
finite, the biduality morphism `L̃ ⟶ R𝓗om(R𝓗om(L̃, ω̃), ω̃)` on `Spec R` is an isomorphism. -/
theorem isIso_derivedBiduality_derivedTilde
    (ω L : DerivedCategory (ModuleCat.{u} R)) (hω : Dualizing.IsDualizingComplex ω)
    (hL : ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L)) :
    IsIso (derivedBiduality (Spec R).sheaf ((tilde.functor R).mapDerivedCategory.obj ω)
      ((tilde.functor R).mapDerivedCategory.obj L)) := by
  let t : Triangulated.TStructure (DerivedCategory (ModuleCat.{u} R)) :=
    DerivedCategory.TStructure.t
  let d₀ := StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))
  let tl := (tilde.functor R).mapDerivedCategory
  let K := tl.obj ω
  let Dh := (derivedSheafHom (Spec R).sheaf).flip.obj K
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  have hωge : ω.IsGE a := StacksDraft.InjectiveDimension.isGE_of_hasInjectiveAmplitude ω a b hamp
  have hωplus : t.plus ω := ⟨a, hωge⟩
  have hKge : K.IsGE a := Stacks.Sites.FibredCategory.isGE_mapDerivedCategory_obj _ ω a
  have hDle : ∀ (E : DerivedCategory (ModuleCat.{u} R)) (k : ℤ), E.IsGE k →
      (Dh.obj (op (tl.obj E))).IsLE (b - k) := fun E k hE =>
    isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude R E ω k a b hE hamp
  have hDge : ∀ (X : DerivedCategory (StructureSheafModules (Spec R).sheaf)) (k : ℤ), X.IsLE k →
      (Dh.obj (op X)).IsGE (a - k) := fun X k hX =>
    isGE_derivedSheafHom (Spec R).sheaf X K k a hX hKge
  have pc_of : ∀ (Y : DerivedCategory (ModuleCat.{u} R)) (n : ℤ), Y.IsLE n →
      (∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj Y)) →
      StacksDraft.PseudoCoherence.IsPseudoCoherent Y := fun Y n hY hYf =>
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      Y 0 (R : Type u)).2.1).2 ⟨⟨n, fun i hi => DerivedCategory.isZero_of_isLE Y n i hi⟩, hYf⟩
  refine (DerivedCategory.isIso_iff (C := StructureSheafModules (Spec R).sheaf) _).2 fun i => ?_
  -- the upper truncation `τ_{≤ n} L ⟶ L`
  let n := max i (i + (b - a))
  let TL := (t.triangleLEGE n (n + 1) rfl).obj L
  have hT := tl.map_distinguished TL (t.triangleLEGE_distinguished n (n + 1) rfl L)
  obtain ⟨_, hDD⟩ := exists_distinguished_derivedSheafHom_first (Spec R).sheaf K _
    (exists_distinguished_derivedSheafHom_first (Spec R).sheaf K _ hT).choose_spec
  have hB : TL.obj₃.IsGE (n + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGE (n + 1)).obj L) (n + 1))
  have hBt : (tl.obj TL.obj₃).IsGE (n + 1) :=
    Stacks.Sites.FibredCategory.isGE_mapDerivedCategory_obj _ _ _
  have hDDB : (Dh.obj (op (Dh.obj (op (tl.obj TL.obj₃))))).IsGE (a - (b - (n + 1))) :=
    hDge _ _ (hDle _ _ hB)
  let HF := DerivedCategory.homologyFunctor (StructureSheafModules (Spec R).sheaf) i
  have h₁ : IsIso (HF.map (tl.map TL.mor₁)) :=
    isIso_homology_mor₁ _ hT i (DerivedCategory.isZero_of_isGE _ (n + 1) i (by omega) (hX := hBt))
      (DerivedCategory.isZero_of_isGE _ (n + 1) (i - 1) (by omega) (hX := hBt))
  have h₂ : IsIso (HF.map (Dh.map (Dh.map (tl.map TL.mor₁).op).op)) :=
    isIso_homology_mor₁ _ hDD i
      (DerivedCategory.isZero_of_isGE _ (a - (b - (n + 1))) i (by omega) (hX := hDDB))
      (DerivedCategory.isZero_of_isGE _ (a - (b - (n + 1))) (i - 1) (by omega) (hX := hDDB))
  have hn1 := congrArg HF.map (derivedBiduality_naturality (Spec R).sheaf K (tl.map TL.mor₁))
  have step1 : IsIso (HF.map (derivedBiduality (Spec R).sheaf K (tl.obj TL.obj₁))) ↔
      IsIso (HF.map (derivedBiduality (Spec R).sheaf K (tl.obj L))) :=
    @Stacks.MayerVietoris.CanonicalMapOfComplexes.General.DerivedCSquareData.isIso_iff_of_comp_eq
      _ _ _ _ _ _ _ _ _ _ ((HF.map_comp _ _).symm.trans (hn1.trans (HF.map_comp _ _))).symm h₁ h₂
  -- the lower truncation `τ_{≤ n} L ⟶ τ_{≥ p} τ_{≤ n} L`
  let L₁ := TL.obj₁
  have hL₁le : L₁.IsLE n := inferInstanceAs (t.IsLE ((t.truncLE n).obj L) n)
  have hL₁f := StacksDraft.DerivedHomFiniteness.finite_homology_truncLE L hL n
  let p := min i (i - (b - a))
  let TP := (t.triangleLEGE (p - 1) p (by omega)).obj L₁
  have hT' := tl.map_distinguished TP (t.triangleLEGE_distinguished (p - 1) p (by omega) L₁)
  obtain ⟨_, hDD'⟩ := exists_distinguished_derivedSheafHom_first (Spec R).sheaf K _
    (exists_distinguished_derivedSheafHom_first (Spec R).sheaf K _ hT').choose_spec
  have hA : TP.obj₁.IsLE (p - 1) :=
    inferInstanceAs (t.IsLE ((t.truncLE (p - 1)).obj L₁) (p - 1))
  have hAle : TP.obj₁.IsLE n := inferInstanceAs (t.IsLE ((t.truncLE (p - 1)).obj L₁) n)
  have hAt : (tl.obj TP.obj₁).IsLE (p - 1) := Stacks.Homology.isLE_mapDerivedCategory_obj _ _ _
  have hApc : StacksDraft.PseudoCoherence.IsPseudoCoherent TP.obj₁ :=
    pc_of _ n hAle (StacksDraft.DerivedHomFiniteness.finite_homology_truncLE L₁ hL₁f (p - 1))
  let θ := affinePseudoCoherentDerivedSheafHomIso R TP.obj₁ ω hApc hωplus
  have hP : (d₀.hom.obj (op TP.obj₁, ω)).IsGE (a - (p - 1)) :=
    StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude d₀ _ ω (p - 1) a b hA
      hamp
  have hDDA : (Dh.obj (op (Dh.obj (op (tl.obj TP.obj₁))))).IsLE (b - (a - (p - 1))) := by
    have := hDle _ _ hP
    exact DerivedCategory.TStructure.t.isLE_of_iso (Dh.mapIso θ.op) _
  have h₃ : IsIso (HF.map (tl.map TP.mor₂)) :=
    isIso_homology_mor₂ _ hT' i (DerivedCategory.isZero_of_isLE _ (p - 1) i (by omega) (hX := hAt))
      (DerivedCategory.isZero_of_isLE _ (p - 1) (i + 1) (by omega) (hX := hAt))
  have h₄ : IsIso (HF.map (Dh.map (Dh.map (tl.map TP.mor₂).op).op)) :=
    isIso_homology_mor₂ _ hDD' i
      (DerivedCategory.isZero_of_isLE _ (b - (a - (p - 1))) i (by omega) (hX := hDDA))
      (DerivedCategory.isZero_of_isLE _ (b - (a - (p - 1))) (i + 1) (by omega) (hX := hDDA))
  have hn2 := congrArg HF.map (derivedBiduality_naturality (Spec R).sheaf K (tl.map TP.mor₂))
  have step2 : IsIso (HF.map (derivedBiduality (Spec R).sheaf K (tl.obj L₁))) ↔
      IsIso (HF.map (derivedBiduality (Spec R).sheaf K (tl.obj TP.obj₃))) :=
    @Stacks.MayerVietoris.CanonicalMapOfComplexes.General.DerivedCSquareData.isIso_iff_of_comp_eq
      _ _ _ _ _ _ _ _ _ _ ((HF.map_comp _ _).symm.trans (hn2.trans (HF.map_comp _ _))).symm h₃ h₄
  -- the bounded case
  have hL₄ge : TP.obj₃.IsGE p := inferInstanceAs (t.IsGE ((t.truncGE p).obj L₁) p)
  have hL₄le : TP.obj₃.IsLE n := inferInstanceAs (t.IsLE ((t.truncGE p).obj L₁) n)
  have hb := isIso_derivedBiduality_derivedTilde_of_bounded R ω TP.obj₃ hω p n hL₄ge hL₄le
    (StacksDraft.DerivedHomFiniteness.finite_homology_truncGE L₁ hL₁f p)
  exact step1.1 (step2.2 (Functor.map_isIso HF _))

end Main

end Stacks.Duality

end
