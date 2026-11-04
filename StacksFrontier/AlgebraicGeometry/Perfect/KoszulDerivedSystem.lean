module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.Koszul
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# The derived Koszul system on an affine scheme and its augmentation to the structure sheaf

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  Sheafifying the inverse system of
truncated Koszul complexes `I^•(f₁^e, …, f_r^e)` gives an inverse system `e ↦ Iₑ` of objects of
`D(𝒪_X)`, and the degree-one Koszul differential `K₁(f^{e+1}) → K₀(f^{e+1}) ≅ A` sheafifies to a
compatible system of maps `Iₑ → 𝒪_X`.

The main result is that these maps become isomorphisms after restriction to `U`.  Locally on
`D(fᵢ)` the element `fᵢ` is invertible, so multiplication by `fᵢ^{e+1}` is null-homotopic on the
Koszul complex and the augmentation is a quasi-isomorphism there; since the `D(fᵢ)` cover `U` and
restriction detects isomorphisms of module sheaves on the stalks, the augmentation becomes
invertible after restriction to `U`.

## Main definitions

* `Koszul.DerivedSystem.basicOpens`, `Koszul.DerivedSystem.unionOfBasicOpens` and
  `Koszul.DerivedSystem.basicOpenCover` are the opens `D(fᵢ)`, their union `U` and the covering
  of `U` by them.
* `Koszul.DerivedSystem.derivedCat` is `D(𝒪_X)` and
  `Koszul.DerivedSystem.structureSheafObject` is `𝒪_X` placed in degree zero.
* `Koszul.DerivedSystem.sheafifyModule` is the associated-sheaf functor `M ↦ M̃` and
  `Koszul.DerivedSystem.derivedSheafify` is derived sheafification `D(A) ⥤ D(𝒪_X)`.
* `Koszul.DerivedSystem.koszulDerivedSystem` is the inverse system `I₁ ← I₂ ← I₃ ← ⋯` in
  `D(𝒪_X)`.
* `Koszul.DerivedSystem.koszulIdealAugmentation` is the degree-one Koszul differential, read as
  a map `I^•(f^{e+1}) ⟶ A[0]`, and
  `Koszul.DerivedSystem.canonicalKoszulToStructureSheaf` is its sheafification `Iₑ ⟶ 𝒪_X`.
* `Koszul.DerivedSystem.koszulSystemToStructureSheaf` packages the latter as a morphism from the
  inverse system to the constant system at `𝒪_X`.
* `Koszul.DerivedSystem.restrictionToUnion` is derived restriction `(-)|_U`.

## Main results

* `Koszul.DerivedSystem.koszulIdealAugmentation_transition`: the augmentations are compatible
  with the transition maps of the Koszul system.
* `Koszul.DerivedSystem.restrictionIsoOfUnion`: the isomorphism `𝒪_X|_U ≅ Iₑ|_U` inverse to the
  restriction of `Iₑ → 𝒪_X`, together with
  `Koszul.DerivedSystem.restrictionIsoOfUnion_inv` identifying its inverse.

## Implementation notes

Following the indexing of the Koszul system, the index `e : ℕ` stands for the exponent `e + 1`,
so stage `e` is attached to `I^•(f₁^{e+1}, …, f_r^{e+1})`.  A finite sequence `f₁, …, f_r` is an
ordered `r`-tuple, so the index type is `Fin r`.

The base ring is an object `A` of `CommRingCat`, not a type with a `CommRing` instance passed
through `CommRingCat.of`: every typeclass about `AlgebraicGeometry.tilde.functor` is stated for a
variable of `CommRingCat`, and instance search does not see through `CommRingCat.of`.

The structure sheaf of rings is spelled `(Spec A).ringCatSheaf` and the modules over it
`SheafOfModules (Spec A).ringCatSheaf`; `AlgebraicGeometry.tilde.functor` lands in the
definitionally equal but separately instanced `(Spec A).Modules`, so the laundered
`Koszul.DerivedSystem.sheafifyModule` is used throughout.  `structureSheafObject` is the
degree-zero single functor applied to the unit module, which is the same object as the structure
sheaf complex of the ringed site of `Spec A`.

Derived restriction to an open subspace inverts the quasi-isomorphisms, so it has a total right
derived functor; `homotopyRestriction_hasRightDerivedFunctor` records this, which is why none of
the statements below carries a `HasRightDerivedFunctor` hypothesis.

## References

* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 08CY](https://stacks.math.columbia.edu/tag/08CY)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe w' w u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of restriction to an open subspace -/

/-- Restriction to an open subspace is left exact: it is a right adjoint. -/
public instance jStar_preservesFiniteLimits {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (jStar U O) :=
  have : (jStar U O).IsRightAdjoint := (jShriekAdjunction U O).isRightAdjoint
  inferInstance

/-- Restriction to an open subspace is right exact: it is a left adjoint. -/
public instance jStar_preservesFiniteColimits {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    PreservesFiniteColimits (jStar U O) :=
  have : (jStar U O).IsLeftAdjoint := (jStarAdjunction U O).isLeftAdjoint
  inferInstance

/-- Restriction to an open subspace has a total right derived functor: being exact, it inverts
the quasi-isomorphisms already after passing to the derived category. -/
public instance homotopyRestriction_hasRightDerivedFunctor {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (resRing U O))] :
    (homotopyRestriction O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) := by
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  have h : W.IsInvertedBy (homotopyRestriction O U) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso W
        (jStar U O).mapDerivedCategoryFactorsh).mp
      (MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
        (Localization.inverts DerivedCategory.Qh W) (jStar U O).mapDerivedCategory)
  have := Functor.hasPointwiseRightDerivedFunctor_of_inverts (homotopyRestriction O U) h
  infer_instance

/-! ### The standing data -/

variable {A : CommRingCat.{u}} {r : ℕ}

/-- The basic opens `D(f₁), …, D(f_r)` of `X = Spec A`. -/
public abbrev basicOpens (f : Fin r → A) : Fin r → (Spec A).Opens :=
  fun i ↦ PrimeSpectrum.basicOpen (f i)

/-- The open `U = D(f₁) ∪ ⋯ ∪ D(f_r)` of `X = Spec A`. -/
public abbrev unionOfBasicOpens (f : Fin r → A) : (Spec A).Opens := ⨆ i, basicOpens f i

/-- The covering of `U = D(f₁) ∪ ⋯ ∪ D(f_r)` by the basic opens `D(fᵢ)`. -/
public abbrev basicOpenCover (f : Fin r → A) : (unionOfBasicOpens f).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (basicOpens f)

/-- The unbounded derived category `D(𝒪_X)` of modules on `X = Spec A`. -/
public abbrev derivedCat (A : CommRingCat.{u}) :=
  DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)

/-- The associated-sheaf functor `M ↦ M̃` on `X = Spec A`, with its codomain spelled as the
modules over `(Spec A).ringCatSheaf`.  The two spellings of that category are the same type but
carry separately declared instances, and this is the one in which the derived category of
`𝒪_X`-modules above is taken. -/
public def sheafifyModule (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ SheafOfModules.{u} (Spec A).ringCatSheaf :=
  tilde.functor A

/-- Sheafification of modules is additive. -/
public instance sheafifyModule_additive (A : CommRingCat.{u}) : (sheafifyModule A).Additive :=
  inferInstanceAs ((tilde.functor A).Additive)

/-- Sheafification of modules is left exact, the stalk of `M̃` at a prime being a localization
of `M`. -/
public instance sheafifyModule_preservesFiniteLimits (A : CommRingCat.{u}) :
    PreservesFiniteLimits (sheafifyModule A) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits A

/-- Sheafification of modules is right exact, being a left adjoint. -/
public instance sheafifyModule_preservesFiniteColimits (A : CommRingCat.{u}) :
    PreservesFiniteColimits (sheafifyModule A) :=
  inferInstanceAs (PreservesFiniteColimits (tilde.functor A))

/-- Derived sheafification `D(A) ⥤ D(𝒪_X)`: the exact functor `M ↦ M̃` induces a functor between
the unbounded derived categories. -/
public abbrev derivedSheafify (A : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} A) ⥤ derivedCat A :=
  (sheafifyModule A).mapDerivedCategory

/-- The structure sheaf `𝒪_X`, viewed as an object of `D(𝒪_X)` concentrated in degree `0`. -/
public def structureSheafObject (A : CommRingCat.{u}) : derivedCat A :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (Spec A).ringCatSheaf) 0).obj
    (SheafOfModules.unit (Spec A).ringCatSheaf)

/-- Derived restriction `(-)|_U` to the open `U = D(f₁) ∪ ⋯ ∪ D(f_r)`. -/
public abbrev restrictionToUnion (f : Fin r → A) :
    derivedCat A ⥤
      DerivedCategory (SheafOfModules.{u}
        (resRing (unionOfBasicOpens f) (Spec A).ringCatSheaf)) :=
  derivedRestriction (Spec A).ringCatSheaf (unionOfBasicOpens f)

/-! ### The derived Koszul system -/

/-- The inverse system `I₁ ← I₂ ← I₃ ← ⋯` in `D(𝒪_X)`: the system of truncated Koszul complexes,
extended from nonnegative chain degrees to nonpositive cochain degrees and then sheafified.
Stage `e` is attached to the Koszul ideal complex on the `(e + 1)`st powers of `f`. -/
public def koszulDerivedSystem (f : Fin r → A) : ℕᵒᵖ ⥤ derivedCat A :=
  (Koszul.koszulIdealComplexSystem f).diagram ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A) ⋙
    DerivedCategory.Q ⋙ derivedSheafify A

/-- The Koszul differential from degree one to degree zero, read as the augmentation
`I^•(f₁^{e+1}, …, f_r^{e+1}) ⟶ A[0]` of the Koszul ideal complex. -/
public def koszulIdealAugmentation (f : Fin r → A) (e : ℕ) :
    Koszul.koszulIdealComplexPower f e ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A) := by
  let K := Koszul.seqComplex fun i ↦ f i ^ (e + 1)
  let d : (Koszul.koszulIdealComplexPower f e).X 0 ⟶ ModuleCat.of A A :=
    K.d 1 0 ≫ ModuleCat.ofHom ((exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap)
  have hd : (Koszul.koszulIdealComplexPower f e).d 1 0 ≫ d = 0 := by
    change (-K.d 2 1) ≫ (K.d 1 0 ≫ _) = 0
    rw [Preadditive.neg_comp, neg_eq_zero]
    exact (K.d_comp_d_assoc 2 1 0 _).trans Limits.zero_comp
  exact (ChainComplex.toSingle₀Equiv _ _).symm ⟨d, hd⟩

/-- Sheafifying the ring in degree zero gives the structure sheaf. -/
public def derivedRingObjectIso (A : CommRingCat.{u}) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A) ⋙
        DerivedCategory.Q ⋙ derivedSheafify A).obj
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A))) ≅
      structureSheafObject A := by
  let M := ModuleCat.of A A
  let T := sheafifyModule A
  let C := SheafOfModules.{u} (Spec A).ringCatSheaf
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  exact (derivedSheafify A).mapIso (DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso (e := ComplexShape.embeddingDownNat)
        (X := M) 0 0 rfl)) ≪≫
    T.mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app (T.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor C 0).mapIso tildeSelf

/-- The component at stage `e` of the canonical system of maps `Iₑ ⟶ 𝒪_X`. -/
public def canonicalKoszulToStructureSheaf (f : Fin r → A) (e : ℕ) :
    (koszulDerivedSystem f).obj (op e) ⟶ structureSheafObject A :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A) ⋙
      DerivedCategory.Q ⋙ derivedSheafify A).map (koszulIdealAugmentation f e) ≫
    (derivedRingObjectIso A).hom

/-- The canonical map `Iₑ ⟶ 𝒪_X`, with the three stages of its construction spelled out. -/
public lemma canonicalKoszulToStructureSheaf_eq (f : Fin r → A) (e : ℕ) :
    canonicalKoszulToStructureSheaf f e =
      (derivedSheafify A).map (DerivedCategory.Q.map
          ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).map
            (koszulIdealAugmentation f e))) ≫ (derivedRingObjectIso A).hom :=
  rfl

/-- The augmentations to the ring in degree zero are compatible with the transition maps of the
Koszul system. -/
public lemma koszulIdealAugmentation_transition (f : Fin r → A) (e : ℕ) :
    (Koszul.koszulIdealComplexSystem f).transition e ≫
      koszulIdealAugmentation f e = koszulIdealAugmentation f (e + 1) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change ((Koszul.koszulIdealComplexSystem f).transition e).f 0 ≫
      (koszulIdealAugmentation f e).f 0 = (koszulIdealAugmentation f (e + 1)).f 0
  rw [Koszul.KoszulIdealComplexSystem.transition_f]
  apply ModuleCat.hom_ext
  ext x
  dsimp only [Koszul.koszulIdealComplexPower, Koszul.koszulIdealComplex,
    Koszul.seqComplex, Koszul.complex] at x ⊢
  change exteriorPower.zeroEquiv A (Fin r → A)
      (Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (e + 1))) 0
        (exteriorPower.map 1 (Koszul.coordinatewiseMul f) x)) =
    exteriorPower.zeroEquiv A (Fin r → A)
      (Koszul.d (Koszul.seqDual (fun i ↦ f i ^ (e + 2))) 0 x)
  rw [Koszul.zeroEquiv_d_zero]
  conv_rhs => rw [Koszul.zeroEquiv_d_zero]
  have hx := congrArg (fun g : (⋀[A]^1 (Fin r → A)) →ₗ[A] (Fin r → A) => g x)
    (exteriorPower.oneEquiv_naturality (Koszul.coordinatewiseMul f))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
  have hx' : (exteriorPower.oneEquiv A (Fin r → A)).toLinearMap
      (exteriorPower.map 1 (Koszul.coordinatewiseMul f) x) =
      Koszul.coordinatewiseMul f
        ((exteriorPower.oneEquiv A (Fin r → A)).toLinearMap x) :=
    hx
  change Koszul.seqDual (fun i ↦ f i ^ (e + 1))
      ((exteriorPower.oneEquiv A (Fin r → A)).toLinearMap
        (exteriorPower.map 1 (Koszul.coordinatewiseMul f) x)) =
    Koszul.seqDual (fun i ↦ f i ^ (e + 2))
      ((exteriorPower.oneEquiv A (Fin r → A)).toLinearMap x)
  rw [hx']
  simp [Koszul.seqDual_apply, Koszul.coordinatewiseMul, pow_succ',
    mul_comm, mul_left_comm, mul_assoc]

/-- The compatible system of maps `Iₑ ⟶ 𝒪_X`, as a morphism from the derived Koszul system to
the constant system at the structure sheaf. -/
public def koszulSystemToStructureSheaf (f : Fin r → A) :
    koszulDerivedSystem f ⟶ (Functor.const ℕᵒᵖ).obj (structureSheafObject A) := by
  let C := (Koszul.koszulIdealComplexSystem f).diagram
  let G := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let F := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A) ⋙
    DerivedCategory.Q ⋙ derivedSheafify A
  let α : C ⟶ (Functor.const ℕᵒᵖ).obj G := NatTrans.ofOpSequence
    (fun e ↦ koszulIdealAugmentation f e)
    (fun e ↦ by
      dsimp only [C, Koszul.KoszulIdealComplexSystem.diagram]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.const_obj_map]
      convert koszulIdealAugmentation_transition f e using 1 <;> rfl)
  let β : (Functor.const ℕᵒᵖ).obj G ⋙ F ⟶
      (Functor.const ℕᵒᵖ).obj (structureSheafObject A) := {
    app := fun _ ↦ (derivedRingObjectIso A).hom
    naturality := by intro i j g; simp }
  simpa only [koszulDerivedSystem, C, G, F] using
    (Functor.whiskerRight α F ≫ β)

/-- The components of the system of maps to the structure sheaf are the sheafified Koszul
augmentations. -/
public lemma koszulSystemToStructureSheaf_app (f : Fin r → A) (e : ℕ) :
    (koszulSystemToStructureSheaf f).app (op e) =
      canonicalKoszulToStructureSheaf f e :=
  rfl

/-! ### Local contractibility of the Koszul augmentation -/

/-- Multiplication by `fᵢ^{e+1}` factors through the augmentation `I^•(f^{e+1}) ⟶ A[0]` in both
directions, the second time up to homotopy: the Koszul complex on a sequence is annihilated up to
homotopy by each member of the sequence. -/
private lemma koszulIdealAugmentation_scalar_homotopy
    (f : Fin r → A) (i : Fin r) (e : ℕ) :
    ∃ s : (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A) ⟶
        Koszul.koszulIdealComplexPower f e,
      s ≫ koszulIdealAugmentation f e = f i ^ (e + 1) • 𝟙 _ ∧
      Nonempty (Homotopy (koszulIdealAugmentation f e ≫ s)
        (f i ^ (e + 1) • 𝟙 _)) := by
  let g : Fin r → A := fun j ↦ f j ^ (e + 1)
  let K := Koszul.seqComplex g
  let I := Koszul.koszulIdealComplexPower f e
  let L := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let α := koszulIdealAugmentation f e
  obtain ⟨hcontr⟩ :=
    (Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator g).1 i
  have hzero : hcontr.hom 0 1 ≫ K.d 1 0 = g i • 𝟙 (K.X 0) := by
    have hc := hcontr.comm 0
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hc
    simpa using hc.symm
  let u : ModuleCat.of A A ⟶ K.X 0 :=
    ModuleCat.ofHom ((exteriorPower.zeroEquiv A (Fin r → A)).symm.toLinearMap)
  let v : K.X 0 ⟶ ModuleCat.of A A :=
    ModuleCat.ofHom ((exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap)
  have huv : u ≫ v = 𝟙 (ModuleCat.of A A) := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    (exteriorPower.zeroEquiv A (Fin r → A)).apply_symm_apply x
  have hvu : v ≫ u = 𝟙 (K.X 0) := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    (exteriorPower.zeroEquiv A (Fin r → A)).symm_apply_apply x
  let s : L ⟶ I :=
    (ChainComplex.fromSingle₀Equiv I (ModuleCat.of A A)).symm (u ≫ hcontr.hom 0 1)
  have hstep : (u ≫ hcontr.hom 0 1) ≫ (K.d 1 0 ≫ v) = g i • 𝟙 (ModuleCat.of A A) := by
    rw [Category.assoc, ← Category.assoc (hcontr.hom 0 1), hzero,
      Linear.smul_comp, Category.id_comp, Linear.comp_smul, huv]
  have hsα : s ≫ α = g i • 𝟙 L :=
    (ChainComplex.fromSingle₀Equiv L (ModuleCat.of A A)).injective hstep
  have hc (m : ℕ) : g i • 𝟙 (K.X (m + 1)) = K.d (m + 1) m ≫ hcontr.hom m (m + 1) +
      hcontr.hom (m + 1) (m + 2) ≫ K.d (m + 2) (m + 1) := by
    have h := hcontr.comm (m + 1)
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
    simpa using h
  let Hhom : ∀ n m : ℕ, I.X n ⟶ I.X m := fun n m ↦ hcontr.hom (n + 1) (m + 1)
  let H : Homotopy (α ≫ s) (g i • 𝟙 I) := {
    hom := Hhom
    zero := by
      intro n m hnm
      change hcontr.hom (n + 1) (m + 1) = 0
      apply hcontr.zero
      simpa only [ComplexShape.down_Rel, Nat.add_right_cancel_iff] using hnm
    comm := by
      intro n
      cases n with
      | zero =>
          dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
          simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
          change (K.d 1 0 ≫ v) ≫ (u ≫ hcontr.hom 0 1) =
            ((0 : K.X 1 ⟶ K.X 1) + hcontr.hom 1 2 ≫ (-K.d 2 1)) + g i • 𝟙 (K.X 1)
          have hlhs : (K.d 1 0 ≫ v) ≫ (u ≫ hcontr.hom 0 1) =
              K.d 1 0 ≫ hcontr.hom 0 1 := by
            rw [Category.assoc, ← Category.assoc v u, hvu, Category.id_comp]
          rw [hlhs, hc 0, Preadditive.comp_neg]
          abel
      | succ n =>
          dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
          simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
          rw [ChainComplex.fromSingle₀Equiv_symm_apply_f_succ, Limits.comp_zero]
          change 0 = ((-K.d (n + 2) (n + 1)) ≫
              hcontr.hom (n + 1) (n + 2) + hcontr.hom (n + 2) (n + 3) ≫
                (-K.d (n + 3) (n + 2))) + g i • 𝟙 (K.X (n + 2))
          rw [hc (n + 1), Preadditive.neg_comp, Preadditive.comp_neg]
          abel }
  exact ⟨s, hsα, ⟨H⟩⟩

/-- A functor carries a composite to an isomorphism as soon as it carries both factors to
isomorphisms. -/
private lemma isIso_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ha : IsIso (F.map a)) (hb : IsIso (F.map b)) : IsIso (F.map (a ≫ b)) := by
  have := ha
  have := hb
  rw [F.map_comp]
  infer_instance


/-- A morphism both of whose composites with a second morphism are invertible is itself
invertible. -/
private lemma isIso_of_two_composites {C : Type*} [Category C]
    {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) [IsIso (a ≫ b)] [IsIso (b ≫ a)] :
    IsIso a := by
  have : Epi a := epi_of_epi b a
  refine ⟨⟨b ≫ inv (a ≫ b), ?_, ?_⟩⟩
  · simp [← Category.assoc]
  · apply (cancel_epi a).mp
    simp [← Category.assoc]

/-- If an additive functor makes multiplication by `fᵢ^{e+1}` invertible on both the Koszul ideal
complex and the ring in degree zero, then it makes the Koszul augmentation a
quasi-isomorphism. -/
private lemma quasiIso_map_koszulIdealAugmentation
    {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat.{u} A ⥤ C) [F.Additive]
    (f : Fin r → A) (i : Fin r) (e : ℕ)
    (hI : IsIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (f i ^ (e + 1) • 𝟙 (Koszul.koszulIdealComplexPower f e))))
    (hA : IsIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (f i ^ (e + 1) • 𝟙 ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A A))))) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (koszulIdealAugmentation f e)) := by
  let FC := F.mapHomologicalComplex (ComplexShape.down ℕ)
  let Q := HomotopyCategory.quotient C (ComplexShape.down ℕ)
  obtain ⟨s, hs, ⟨H⟩⟩ := koszulIdealAugmentation_scalar_homotopy f i e
  let a := FC.map (koszulIdealAugmentation f e)
  let b := FC.map s
  have ha : Q.map a ≫ Q.map b = Q.map (FC.map
      (f i ^ (e + 1) • 𝟙 (Koszul.koszulIdealComplexPower f e))) := by
    rw [← Q.map_comp, ← FC.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy H)
  have hb : Q.map b ≫ Q.map a = Q.map (FC.map
      (f i ^ (e + 1) • 𝟙 ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A A)))) := by
    rw [← Q.map_comp, ← FC.map_comp, hs]
  have : IsIso (Q.map a ≫ Q.map b) := by rw [ha]; infer_instance
  have : IsIso (Q.map b ≫ Q.map a) := by rw [hb]; infer_instance
  have : IsIso (Q.map a) := isIso_of_two_composites _ (Q.map b)
  exact homotopyEquivalences_le_quasiIso C _ _ <|
    HomotopyCategory.inverseImage_quotient_isomorphisms C _ ▸ inferInstanceAs (IsIso (Q.map a))

/-! ### Multiplication by a scalar on a sheaf of modules on an affine scheme -/

/-- Multiplication by an element of `R` on the sheaf of `R`-modules underlying an
`𝒪_{Spec R}`-module. -/
private def specScalarSheaf {R : CommRingCat.{u}} (a : R) (M : (Spec R).Modules) :
    (modulesSpecToSheaf (R := R)).obj M ⟶ (modulesSpecToSheaf (R := R)).obj M :=
  ⟨{ app := fun _ ↦ a • 𝟙 _
     naturality := by intros; simp [Linear.comp_smul, Linear.smul_comp] }⟩

/-- Multiplication by an element of `R` on an `𝒪_{Spec R}`-module. -/
private def specScalar {R : CommRingCat.{u}} (a : R) (M : (Spec R).Modules) : M ⟶ M :=
  (modulesSpecToSheaf (R := R)).preimage (specScalarSheaf a M)

/-- Multiplication by `a` acts on sections as multiplication by `a`. -/
private lemma specScalar_app {R : CommRingCat.{u}} (a : R) (M : (Spec R).Modules)
    (U : (Spec R).Opens) (x : Γ(M, U)) :
    (specScalar a M).val.app (op U) x = a • x := by
  have h := (modulesSpecToSheaf (R := R)).map_preimage (specScalarSheaf a M)
  have h' := congrArg (fun q => (q.hom.app (op U)).hom x) h
  exact h'

/-- Sheafification turns multiplication by `a` on a module into multiplication by `a` on the
associated sheaf. -/
private lemma tilde_map_smul_id {R : CommRingCat.{u}} (a : R) (M : ModuleCat.{u} R) :
    (tilde.functor R).map (a • 𝟙 M) =
      specScalar a ((tilde.functor R).obj M) := by
  apply (tilde.adjunction (R := R)).homEquiv M _ |>.injective
  change (tilde.adjunction (R := R)).unit.app M ≫
      (moduleSpecΓFunctor (R := R)).map
        ((tilde.functor R).map (a • 𝟙 M)) = _
  have hn := (tilde.adjunction (R := R)).unit.naturality (a • 𝟙 M)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn]
  ext x
  change (tilde.adjunction (R := R)).unit.app M (a • x) =
    (specScalar a ((tilde.functor R).obj M)).val.app (op ⊤)
      ((tilde.adjunction (R := R)).unit.app M x)
  exact (((tilde.adjunction (R := R)).unit.app M).hom.map_smul a x).trans
    (specScalar_app a ((tilde.functor R).obj M) ⊤ _).symm

/-- On an open contained in `D(a)` multiplication by `a` becomes invertible after restriction:
`a` acts invertibly on the sections over every open contained in `D(a)`. -/
private lemma specScalar_jStar_isIso {R : CommRingCat.{u}} (a : R)
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (hU : U ≤ PrimeSpectrum.basicOpen a) :
    IsIso ((jStar U (Spec R).ringCatSheaf).map (specScalar a M)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (fun x : Γ(M, (TopCat.Presheaf.imF U).obj V.unop) =>
    (specScalar a M).val.app (op ((TopCat.Presheaf.imF U).obj V.unop)) x)
  simp_rw [specScalar_app]
  have hV : (TopCat.Presheaf.imF U).obj V.unop ≤ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  exact (Module.End.isUnit_iff _).mp
    (M.isUnit_algebraMap_end_of_le_basicOpen a (hV.trans hU))

/-- Sheafification followed by restriction to an open subset. -/
private abbrev tildeRestrict (U : (Spec A).Opens) :
    ModuleCat.{u} A ⥤
      SheafOfModules.{u} (resRing U (Spec A).ringCatSheaf) :=
  sheafifyModule A ⋙ jStar U (Spec A).ringCatSheaf

/-- On an open contained in `D(fᵢ)` the sheafified, restricted Koszul augmentation is a
quasi-isomorphism: there multiplication by `fᵢ^{e+1}` is invertible, and the augmentation
becomes invertible in the homotopy category. -/
private lemma koszulIdealAugmentation_restrict_quasiIso
    (f : Fin r → A) (i : Fin r) (e : ℕ)
    (U : (Spec A).Opens) (hU : U ≤ basicOpens f i) :
    QuasiIso (((tildeRestrict U).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (koszulIdealAugmentation f e)) := by
  have hpow : U ≤ PrimeSpectrum.basicOpen (f i ^ (e + 1)) := by
    rw [PrimeSpectrum.basicOpen_pow _ _ (Nat.zero_lt_succ e)]
    exact hU
  have h (K : ChainComplex (ModuleCat.{u} A) ℕ) :
      IsIso (((tildeRestrict U).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (f i ^ (e + 1) • 𝟙 K)) := by
    have : ∀ n, IsIso ((((tildeRestrict U).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (f i ^ (e + 1) • 𝟙 K)).f n) := by
      intro n
      change IsIso ((jStar U (Spec A).ringCatSheaf).map
        ((tilde.functor A).map (f i ^ (e + 1) • 𝟙 (K.X n))))
      rw [tilde_map_smul_id]
      exact specScalar_jStar_isIso _ _ U hpow
    exact HomologicalComplex.Hom.isIso_of_components _
  exact quasiIso_map_koszulIdealAugmentation (tildeRestrict U) f i e (h _) (h _)

/-! ### Restriction detects isomorphisms on an open covering -/

/-- A morphism of module sheaves which becomes invertible after restriction to an open induces
isomorphisms on the stalks at the points of that open. -/
private lemma isIso_stalk_of_isIso_restrict {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : Opens X) {M N : SheafOfModules.{u} O} (h : M ⟶ N)
    (hh : IsIso ((jStar V O).map h)) (x : X) (hx : x ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toAb O).map h)) := by
  have hab : IsIso ((toAb (resRing V O)).map ((jStar V O).map h)) :=
    Functor.map_isIso _ _
  have hrestr : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : (Opens.toTopCat X).obj V)).map
        (Functor.whiskerLeft (TopCat.Presheaf.imF V).op ((toAb O).map h))) := by
    rw [← toAb_jStar_map V O h]
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ hab
  exact (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff V _ _
    ((toAb O).map h) ⟨x, hx⟩).mp hrestr

/-- A morphism of module sheaves which becomes invertible after restriction to each member of a
family of opens becomes invertible after restriction to their union: both reductions pass through
the stalks at the points of the union. -/
private lemma isIso_jStar_map_of_cover {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {ι : Type*} (V : ι → Opens X) {M N : SheafOfModules.{u} O} (h : M ⟶ N)
    (hV : ∀ i, IsIso ((jStar (V i) O).map h)) :
    IsIso ((jStar (⨆ i, V i) O).map h) := by
  apply isIso_of_stalk_isIso (resRing (⨆ i, V i) O)
  intro y
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
  have hstalk := isIso_stalk_of_isIso_restrict O (V i) h (hV i) y.1 hi
  have hw := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff (⨆ i, V i) _ _
    ((toAb O).map h) y).mpr hstalk
  rw [← toAb_jStar_map (⨆ i, V i) O h] at hw
  exact hw

/-- **Derived restriction to an open agrees with the functor induced on derived categories by the
exact restriction functor**, for every sheaf of rings on every topological space.  Restriction is
exact (`jStar_preservesFiniteLimits` and `jStar_preservesFiniteColimits` above), so the functor it
induces on derived categories already inverts the quasi-isomorphisms and is therefore a right
derived functor of restriction read on homotopy categories; the comparison is the uniqueness of a
right derived functor.

Nothing in that argument is about `Spec A`, so the statement is made for an arbitrary sheaf of
rings; `derivedRestrictionMapIso` below is the special case this file consumes. -/
public def derivedRestrictionMapIsoOfRingSheaf {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (U : Opens Y) :
    derivedRestriction O U ≅ (jStar U O).mapDerivedCategory := by
  let J := jStar U O
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  letI := Functor.isRightDerivedFunctor_of_inverts W
    J.mapDerivedCategory J.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedNatIso (derivedRestriction O U) J.mapDerivedCategory
    ((homotopyRestriction O U).totalRightDerivedUnit DerivedCategory.Qh W)
    J.mapDerivedCategoryFactorsh.inv W (Iso.refl _)

/-- Derived restriction to an open agrees with the functor induced on derived categories by the
exact restriction functor: both are right derived functors of restriction on homotopy
categories. -/
def derivedRestrictionIsoMapDerivedCategory (U : (Spec A).Opens) :
    derivedRestriction (Spec A).ringCatSheaf U ≅
      (jStar U (Spec A).ringCatSheaf).mapDerivedCategory := by
  let O := (Spec A).ringCatSheaf
  let J := jStar U O
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  letI := Functor.isRightDerivedFunctor_of_inverts W
    J.mapDerivedCategory J.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedNatIso (derivedRestriction O U) J.mapDerivedCategory
    ((homotopyRestriction O U).totalRightDerivedUnit DerivedCategory.Qh W)
    J.mapDerivedCategoryFactorsh.inv W (Iso.refl _)

/-- Derived restriction to an open agrees with the functor induced on derived categories by the
exact restriction functor. -/
private def derivedRestrictionMapIso (U : (Spec A).Opens) :
    derivedRestriction (Spec A).ringCatSheaf U ≅
      (jStar U (Spec A).ringCatSheaf).mapDerivedCategory :=
  derivedRestrictionIsoMapDerivedCategory U

/-! ### The augmentation becomes invertible after restriction to `U` -/

/-- Outside the image of the embedding `down ℕ ↪ up ℤ` both extended complexes are acyclic, so
the extended Koszul augmentation is an isomorphism on cohomology there. -/
private lemma isIso_homologyMap_extend_of_notMem (f : Fin r → A) (e : ℕ) (n : ℤ)
    (hn : ∀ j : ℕ, ComplexShape.embeddingDownNat.f j ≠ n) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (koszulIdealAugmentation f e)
        ComplexShape.embeddingDownNat) n) := by
  have hz : ∀ K : ChainComplex (ModuleCat.{u} A) ℕ,
      IsZero ((K.extend ComplexShape.embeddingDownNat).homology n) := by
    intro K
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomologicalComplex.extend_exactAt K ComplexShape.embeddingDownNat n hn
  exact ⟨⟨0, (hz _).eq_of_src _ _, (hz _).eq_of_src _ _⟩⟩

/-- On an open contained in `D(fᵢ)`, sheafifying and restricting turns the extended Koszul
augmentation into an isomorphism on cohomology in every degree: in the degrees coming from
`down ℕ` this is the local contractibility of the Koszul complex, and the remaining degrees are
acyclic. -/
private lemma isIso_tildeRestrict_homologyMap_extend (f : Fin r → A) (i : Fin r) (e : ℕ)
    (V : (Spec A).Opens) (hV : V ≤ basicOpens f i) (n : ℤ) :
    IsIso ((tildeRestrict V).map
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (koszulIdealAugmentation f e)
          ComplexShape.embeddingDownNat) n)) := by
  by_cases hn : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = n
  · obtain ⟨j, rfl⟩ := hn
    have hq := koszulIdealAugmentation_restrict_quasiIso f i e V hV
    have h1 := hq.quasiIsoAt j
    rw [quasiIsoAt_iff_isIso_homologyMap] at h1
    have h2 : IsIso ((tildeRestrict V).map
        (HomologicalComplex.homologyMap (koszulIdealAugmentation f e) j)) :=
      (NatIso.isIso_map_iff
        ((tildeRestrict V).mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) j)
        (koszulIdealAugmentation f e)).mp h1
    have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := koszulIdealAugmentation f e) (e := ComplexShape.embeddingDownNat)
      (hj' := (rfl : ComplexShape.embeddingDownNat.f j = _))
    have w := congrArg (tildeRestrict V).map hnat
    rw [Functor.map_comp, Functor.map_comp] at w
    have hf : (tildeRestrict V).map (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (koszulIdealAugmentation f e)
            ComplexShape.embeddingDownNat) (ComplexShape.embeddingDownNat.f j)) =
        ((tildeRestrict V).map (HomologicalComplex.extendHomologyIso
              (Koszul.koszulIdealComplexPower f e) ComplexShape.embeddingDownNat rfl).hom ≫
            (tildeRestrict V).map
              (HomologicalComplex.homologyMap (koszulIdealAugmentation f e) j)) ≫
          CategoryTheory.inv ((tildeRestrict V).map (HomologicalComplex.extendHomologyIso
            ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A))
            ComplexShape.embeddingDownNat rfl).hom) := by
      rw [← w]
      simp
    rw [hf]
    infer_instance
  · have := isIso_homologyMap_extend_of_notMem f e n (fun j hj ↦ hn ⟨j, hj⟩)
    exact Functor.map_isIso _ _

/-- The cohomology sheaves of the canonical map `Iₑ → 𝒪_X` become isomorphisms after restriction
to `U = D(f₁) ∪ ⋯ ∪ D(f_r)`: each `D(fᵢ)` makes them isomorphisms, and restriction detects
isomorphisms on an open covering. -/
private lemma isIso_jStar_homology_canonical (f : Fin r → A) (e : ℕ) (n : ℤ) :
    IsIso ((jStar (unionOfBasicOpens f) (Spec A).ringCatSheaf).map
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Spec A).ringCatSheaf) n).map
        (canonicalKoszulToStructureSheaf f e))) := by
  let O := (Spec A).ringCatSheaf
  let J := jStar (unionOfBasicOpens f) O
  let T := sheafifyModule A
  let Ex := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)
  let w := DerivedCategory.Q.map (Ex.map (koszulIdealAugmentation f e))
  have key : IsIso (J.map (T.map (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (koszulIdealAugmentation f e)
        ComplexShape.embeddingDownNat) n))) :=
    isIso_jStar_map_of_cover O (basicOpens f) _ (fun i ↦
      isIso_tildeRestrict_homologyMap_extend f i e (basicOpens f i) le_rfl n)
  have step2 : IsIso (J.map (T.map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map w))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n) (T ⋙ J))
        (Ex.map (koszulIdealAugmentation f e))).mpr key
  have step3 : IsIso (J.map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map
        ((derivedSheafify A).map w))) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (T.mapDerivedCategoryHomologyIso n) J) w).mpr step2
  rw [canonicalKoszulToStructureSheaf_eq]
  exact (Functor.map_comp (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n ⋙ J)
    _ _).symm ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ step3 (Functor.map_isIso _ _)

/-- Restriction to `U` turns the canonical map `Iₑ → 𝒪_X` into an isomorphism: it is an
isomorphism in the derived category exactly when it is one on every cohomology sheaf. -/
public lemma isIso_restrictionToUnion_map_canonical (f : Fin r → A) (e : ℕ) :
    IsIso ((restrictionToUnion f).map (canonicalKoszulToStructureSheaf f e)) := by
  have h : IsIso ((jStar (unionOfBasicOpens f)
      (Spec A).ringCatSheaf).mapDerivedCategory.map
        (canonicalKoszulToStructureSheaf f e)) := by
    rw [Functor.isIso_mapDerivedCategory_map_iff]
    intro n
    exact isIso_jStar_homology_canonical f e n
  exact (NatIso.isIso_map_iff (derivedRestrictionMapIso (unionOfBasicOpens f))
    (canonicalKoszulToStructureSheaf f e)).mpr h

/-- **The maps `Iₑ → 𝒪_X` become isomorphisms after restriction to `U`.**  This is the inverse
isomorphism `𝒪_X|_U ≅ Iₑ|_U`. -/
public def restrictionIsoOfUnion (f : Fin r → A) (e : ℕ) :
    (restrictionToUnion f).obj (structureSheafObject A) ≅
      (restrictionToUnion f).obj ((koszulDerivedSystem f).obj (op e)) :=
  have := isIso_restrictionToUnion_map_canonical f e
  (asIso ((restrictionToUnion f).map (canonicalKoszulToStructureSheaf f e))).symm

/-- `restrictionIsoOfUnion` is inverse to the restriction of the canonical map
`Iₑ → 𝒪_X`. -/
public lemma restrictionIsoOfUnion_inv (f : Fin r → A) (e : ℕ) :
    (restrictionIsoOfUnion f e).inv =
      (restrictionToUnion f).map (canonicalKoszulToStructureSheaf f e) :=
  rfl

end Koszul.DerivedSystem

end
