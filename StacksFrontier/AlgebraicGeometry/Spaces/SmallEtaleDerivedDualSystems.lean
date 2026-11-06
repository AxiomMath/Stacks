module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedBidualNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitHomStable

/-!
# Inverse systems of duals and derived colimits on an algebraic space

This file collects the pieces of the proof of Stacks 0DKY that concern inverse systems of duals
and derived colimits in `D(𝒪_X)` for an algebraic space `X`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedDualOfHom`: the dual `ψ^∨` of a morphism.
* `AlgebraicGeometry.Space.smallEtaleDerivedBidualSystemIso`: biduality `(M^∨)^∨ ≅ M` for a
  system of perfect objects, as an isomorphism of systems.

## Main results

* `AlgebraicGeometry.RingedSite.comp_derivedBidual`: the canonical map `K ⟶ K^∨∨` of a
  ringed site is natural.
* `AlgebraicGeometry.Space.smallEtaleDerivedBidualIso_naturality`: the biduality isomorphism of
  Stacks 08JJ on an algebraic space is natural.
* `isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit_of_hasProduct` (in
  `AlgebraicGeometry.Space`): Stacks 0A0A on an algebraic space.
* `CategoryTheory.Pretriangulated.IsHomotopyColimitWith.comp_strictMono`: Stacks 0CRJ with the
  coprojections.
* `DerivedCategory.isIso_homologyFunctor_map_coprojection`: Stacks 0CRK at a coprojection, and
  `AlgebraicGeometry.Space.isIso_homologyFunctor_map_coprojection_smallEtale` on a space.

## Implementation notes

The derived internal Hom of `X` is that of the equi-universe model of its small étale site, read
through the derived equivalence `AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`;
biduality and Stacks 0A0A are proved on the model and transported.  The model is
`HasDerivedCategory.standard`, seated as in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom`.

`AlgebraicGeometry.Space.smallEtaleDerivedDualOfHom` and
`AlgebraicGeometry.RingedSite.comp_derivedBidual` are, up to binder names,
`AlgebraicGeometry.Space.smallEtaleDerivedDualMap` and
`AlgebraicGeometry.RingedSite.derivedBidual_naturality`; they are to give way to those.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0CRJ](https://stacks.math.columbia.edu/tag/0CRJ)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

/-- A chain of three commutative squares composes: if `φ ≫ a' = a ≫ m`, `m ≫ b' = b ≫ m'` and
`m' ≫ c' = c ≫ d`, then `φ ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ d`.  Stated abstractly so that it
applies to composites whose intermediate objects agree only up to unfolding. -/
theorem CategoryTheory.comp_chain₃ {C : Type*} [Category C] {P P' Q Q' R R' W W' : C}
    {φ : P ⟶ P'} {a : P ⟶ Q} {a' : P' ⟶ Q'} {m : Q ⟶ Q'} {b : Q ⟶ R} {b' : Q' ⟶ R'}
    {m' : R ⟶ R'} {c : R ⟶ W} {c' : R' ⟶ W'} {d : W ⟶ W'}
    (h₁ : φ ≫ a' = a ≫ m) (h₂ : m ≫ b' = b ≫ m') (h₃ : m' ≫ c' = c ≫ d) :
    φ ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ d := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- A chain of two commutative squares composes: if `φ ≫ a' = a ≫ m` and `m ≫ b' = b ≫ m'`,
then `φ ≫ (a' ≫ b') = (a ≫ b) ≫ m'`. -/
theorem CategoryTheory.comp_chain₂ {C : Type*} [Category C] {P P' Q Q' R R' : C}
    {φ : P ⟶ P'} {a : P ⟶ Q} {a' : P' ⟶ Q'} {m : Q ⟶ Q'} {b : Q ⟶ R} {b' : Q' ⟶ R'}
    {m' : R ⟶ R'} (h₁ : φ ≫ a' = a ≫ m) (h₂ : m ≫ b' = b ≫ m') :
    φ ≫ (a' ≫ b') = (a ≫ b) ≫ m' := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- A contravariant functor carries a commutative square to a commutative square. -/
theorem CategoryTheory.Functor.map_op_comm_of_comm {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {P Q Q' R : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ Q'} {d : Q' ⟶ R}
    (h : a ≫ b = c ≫ d) : F.map b.op ≫ F.map a.op = F.map d.op ≫ F.map c.op := by
  rw [← F.map_comp, ← op_comp, h, op_comp, F.map_comp]

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Every system with a direct sum has a derived colimit** (Stacks 090Z): complete the map
`1 - shift` of `∐ Kₙ` to a distinguished triangle. -/
theorem exists_isHomotopyColimitWith_of_hasCoproduct (F : ℕ ⥤ D) [HasCoproduct F.obj] :
    ∃ (L : D) (c : ∀ n, F.obj n ⟶ L), IsHomotopyColimitWith F L c := by
  obtain ⟨L, p, q, hT⟩ := distinguished_cocone_triangle
    (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
    F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1))
  exact ⟨L, fun n => Limits.Sigma.ι F.obj n ≫ p, p, q, hT, fun _ => rfl⟩

/-- **A derived colimit is a derived colimit of every subsystem along a strictly increasing
reindexing** (Stacks 0CRJ), with the coprojections restricted: if `K = hocolim Kₘ` with
coprojections `cₘ` and `n : ℕ → ℕ` is strictly increasing, then `K = hocolim K_{n i}` with
coprojections `c_{n i}`. -/
theorem IsHomotopyColimitWith.comp_strictMono {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) {n : ℕ → ℕ} (hn : StrictMono n)
    [HasCoproduct (hn.monotone.functor ⋙ F).obj] :
    IsHomotopyColimitWith (hn.monotone.functor ⋙ F) K (fun i => c (n i)) := by
  obtain ⟨p, q, hT, hc⟩ := h
  obtain ⟨K', c', h'⟩ := exists_isHomotopyColimitWith_of_hasCoproduct (hn.monotone.functor ⋙ F)
  obtain ⟨p', q', hT', hc'⟩ := id h'
  obtain ⟨e, he⟩ := exists_iso_of_isHomotopyColimit_of_strictMono F hn p q hT p' q' hT'
  refine (h'.of_iso e).congr_coprojections fun i => ?_
  rw [← hc', Category.assoc, he i, hc]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [HasColimitsOfShape ℕ C]
  [HasExactColimitsOfShape ℕ C]

/-- **The coprojections of a derived colimit, in a degree where the system is eventually
constant** (Stacks 0CRK): if `K = hocolim Kₙ` with coprojections `cₙ`, the cohomology `Hⁱ`
commutes with countable direct sums, and `Hⁱ(Kₖ) ⟶ Hⁱ(Kₖ₊₁)` is an isomorphism for every
`k ≥ n`, then `Hⁱ(cₙ) : Hⁱ(Kₙ) ⟶ Hⁱ(K)` is an isomorphism. -/
theorem isIso_homologyFunctor_map_coprojection {F : ℕ ⥤ DerivedCategory C} [HasCoproduct F.obj]
    {K : DerivedCategory C} {c : ∀ n, F.obj n ⟶ K} (hK : IsHomotopyColimitWith F K c) (i : ℤ)
    [PreservesColimitsOfShape (Discrete ℕ) (homologyFunctor C i)] (n : ℕ)
    (h : ∀ k, n ≤ k → IsIso ((homologyFunctor C i).map (F.map (homOfLE (Nat.le_succ k))))) :
    IsIso ((homologyFunctor C i).map (c n)) := by
  obtain ⟨p, q, hT, hc⟩ := hK
  obtain ⟨e, he⟩ := exists_iso_colimit_of_isHomotopyColimit F (homologyFunctor C i) p q hT
  have hd : ∀ d (hnd : n ≤ n + d), IsIso ((F ⋙ homologyFunctor C i).map (homOfLE hnd)) := by
    intro d
    induction d with
    | zero =>
      intro hnd
      rw [show homOfLE hnd = 𝟙 n from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
      infer_instance
    | succ d ih =>
      intro hnd
      have hsplit : homOfLE hnd = homOfLE (Nat.le_add_right n d) ≫ homOfLE (Nat.le_succ (n + d)) :=
        Subsingleton.elim _ _
      rw [hsplit, Functor.map_comp]
      exact IsIso.comp_isIso' (ih (Nat.le_add_right n d)) (h (n + d) (Nat.le_add_right n d))
  have hev : (F ⋙ homologyFunctor C i).IsEventuallyConstantFrom n := by
    intro j f
    obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by have := leOfHom f; omega⟩
    rw [show f = homOfLE (Nat.le_add_right n d) from Subsingleton.elim _ _]
    exact hd d _
  have : IsIso (colimit.ι (F ⋙ homologyFunctor C i) n) :=
    hev.isIso_ι_of_isColimit (colimit.isColimit (F ⋙ homologyFunctor C i))
  have hn := he n
  rw [hc] at hn
  rw [← hn]
  infer_instance

end DerivedCategory

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map to the double derived dual is natural**: for `φ : K ⟶ K'`,
`φ ≫ (K' ⟶ K'^∨∨) = (K ⟶ K^∨∨) ≫ φ^∨∨`. -/
theorem comp_derivedBidual
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : K ⟶ K') :
    φ ≫ derivedBidual X T K' = derivedBidual X T K ≫
      ((derivedSheafHomBifunctor X).map
        (((derivedSheafHomBifunctor X).map φ.op).app (derivedStructureSheaf X)).op).app
          (derivedStructureSheaf X) := by
  have h1 := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_naturality X
    (derivedTensorProductDatumOfSite X T) φ
  have h1' : φ ≫ (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
        (derivedTensorProductDatumOfSite X T) K').inv =
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
        (derivedTensorProductDatumOfSite X T) K).inv ≫
        ((derivedTensorProductDatumOfSite X T).tensor.obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)).map φ := by
    rw [Iso.comp_inv_eq, Category.assoc, h1, Iso.inv_hom_id_assoc]
  have h2 : ((derivedTensorProductDatumOfSite X T).tensor.obj
        (Stacks.DerivedTensor.RingedSite.unitObject X)).map φ ≫
      (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K' =
      (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K ≫
        (T.tensor.obj (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
          (derivedStructureSheaf X))).map φ :=
    (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).naturality φ
  have h3 : (T.tensor.obj (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
        (derivedStructureSheaf X))).map φ ≫
      derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X) K'
        (derivedStructureSheaf X) (derivedStructureSheaf X) =
      derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X) K
        (derivedStructureSheaf X) (derivedStructureSheaf X) ≫
        ((derivedSheafHomBifunctor X).map
          (((derivedSheafHomBifunctor X).map φ.op).app (derivedStructureSheaf X)).op).app
            (derivedStructureSheaf X) := by
    have h := derivedSheafHomEvaluation_natural X T (derivedInternalHomOfBifunctor X) φ
      (𝟙 (derivedStructureSheaf X)) (𝟙 (derivedStructureSheaf X))
    simpa only [derivedTensorMap, op_id, derivedSheafHomMap,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] using h
  rw [derivedBidual_eq, derivedBidual_eq]
  exact CategoryTheory.comp_chain₃ h1' h2 h3

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The derived equivalence with the equi-universe model commutes with the shift. -/
instance commShift_smallEtaleModelDerivedEquivalence_functor :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.CommShift ℤ :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory.CommShift ℤ)

/-- The derived equivalence with the equi-universe model is triangulated. -/
instance isTriangulated_smallEtaleModelDerivedEquivalence_functor :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.IsTriangulated :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory.IsTriangulated)

/-- The inverse of the derived equivalence with the equi-universe model commutes with the
shift. -/
instance commShift_smallEtaleModelDerivedEquivalence_inverse :
    (smallEtaleModelDerivedEquivalence B S hS X).inverse.CommShift ℤ :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory.CommShift ℤ)

/-- The inverse of the derived equivalence with the equi-universe model is triangulated. -/
instance isTriangulated_smallEtaleModelDerivedEquivalence_inverse :
    (smallEtaleModelDerivedEquivalence B S hS X).inverse.IsTriangulated :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory.IsTriangulated)

/-- Colimits over `ℕ` of `𝒪_X`-modules exist and are exact. -/
instance hasExactColimitsOfShape_nat_smallEtaleModules :
    HasExactColimitsOfShape ℕ (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) := by
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
    AB5OfSize_shrink.{0, 0, u, u} _
  exact AB5OfSize.ofShape ℕ

/-- The cohomology sheaves `Hⁱ : D(𝒪_X) ⥤ Mod(𝒪_X)` commute with direct sums indexed by `ℕ`. -/
instance preservesColimitsOfShape_discrete_nat_smallEtaleHomologyFunctor (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i) := by
  have := Stacks.Injectives.derivedCategoryQ_preservesCoproducts
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ULift.{u} ℕ)
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (J := Discrete (ULift.{u} ℕ)) (ComplexShape.up ℤ) i
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ))
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i) :=
    preservesColimitsOfShape_of_natIso
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i).symm
  have : HasColimitsOfShape (Discrete (ULift.{u} ℕ))
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
    inferInstance
  have : HasColimitsOfShape (Discrete (ULift.{u} ℕ))
      (CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :=
    ⟨fun F =>
      have hF : ∀ n : ℤ, HasColimit (F ⋙ HomologicalComplex.eval
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ) n) :=
        fun _ => HasColimitsOfShape.has_colimit _
      ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩⟩
  have := preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i)
    (ULift.{u} ℕ)
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{u, 0} (α := ℕ))) _

/-- `D(𝒪_X)` has products indexed by `ℕ` (Stacks 07D9): the `𝒪_X`-modules form a Grothendieck
abelian category. -/
theorem hasLimitsOfShape_discrete_nat_smallEtaleDerived :
    HasLimitsOfShape (Discrete ℕ)
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  have := Stacks.Injectives.hasProducts_derivedCategory.{u}
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ULift.{u} ℕ)
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-- **The coprojections of a derived colimit in `D(𝒪_X)`, in a degree where the system is
eventually constant** (Stacks 0CRK on an algebraic space). -/
theorem isIso_homologyFunctor_map_coprojection_smallEtale
    {F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    [HasCoproduct F.obj]
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {c : ∀ n, F.obj n ⟶ K} (hK : IsHomotopyColimitWith F K c) (i : ℤ) (n : ℕ)
    (h : ∀ k, n ≤ k → IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i).map
        (F.map (homOfLE (Nat.le_succ k))))) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i).map (c n)) :=
  DerivedCategory.isIso_homologyFunctor_map_coprojection hK i n h

/-- The dual `ψ^∨ : E'^∨ ⟶ E^∨` of a morphism `ψ : E ⟶ E'` of `D(𝒪_X)`. -/
abbrev smallEtaleDerivedDualOfHom
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (ψ : E ⟶ E') : smallEtaleDerivedDual B S hS X E' ⟶ smallEtaleDerivedDual B S hS X E :=
  ((smallEtaleDerivedSheafHom B S hS X).map ψ.op).app
    ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))

/-- The abstract shape of the naturality of the biduality isomorphism: a morphism `u` followed
by an isomorphism `β` is known, and `β` is natural. -/
private theorem comp_bidual_chain {C : Type*} [Category C] {P P' Q Q' R R' : C}
    {x : P ⟶ P'} {u : P ⟶ Q} {u' : P' ⟶ Q'} {ψ : Q ⟶ Q'} {β : Q ⟶ R} {β' : Q' ⟶ R'}
    {w : P ⟶ R} {w' : P' ⟶ R'} {D : R ⟶ R'}
    (hb' : u' ≫ β' = w') (hb : u ≫ β = w) (hn : ψ ≫ β' = β ≫ D) (hs : x ≫ w' = w ≫ D) :
    (x ≫ u') ≫ β' = (u ≫ ψ) ≫ β' := by
  rw [Category.assoc, hb', hs, Category.assoc, hn, ← Category.assoc, hb]

/-- The image on the model of the biduality isomorphism, composed with the canonical map to the
double dual of the model. -/
theorem smallEtaleModelDerivedEquivalence_map_smallEtaleDerivedBidualIso_hom
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.map
        (smallEtaleDerivedBidualIso B S hS X E hE).hom ≫
      RingedSite.derivedBidual (smallEtaleModelRingedSite B S hS X.1 X.2)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (smallEtaleModelRingedSite B S hS X.1 X.2))
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) =
      (smallEtaleModelDerivedDualIso B S hS X (smallEtaleDerivedDual B S hS X E)).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          (smallEtaleModelDerivedDualIso B S hS X E).inv.op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) := by
  have := RingedSite.isIso_derivedBidual_of_isPerfect (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E)
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE)
  simp only [smallEtaleDerivedBidualIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  simp

/-- **The biduality isomorphism `(E^∨)^∨ ≅ E` of a perfect object is natural**: for a morphism
`ψ : E ⟶ E'` of perfect objects, `ψ^∨∨ ≫ (E'^∨∨ ≅ E') = (E^∨∨ ≅ E) ≫ ψ`. -/
theorem smallEtaleDerivedBidualIso_naturality
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (ψ : E ⟶ E') (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (hE' : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E') :
    smallEtaleDerivedDualOfHom B S hS X (smallEtaleDerivedDualOfHom B S hS X ψ) ≫
        (smallEtaleDerivedBidualIso B S hS X E' hE').hom =
      (smallEtaleDerivedBidualIso B S hS X E hE).hom ≫ ψ := by
  apply (smallEtaleModelDerivedEquivalence B S hS X).functor.map_injective
  have := RingedSite.isIso_derivedBidual_of_isPerfect (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E')
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E' hE')
  have n' : (smallEtaleModelDerivedDualIso B S hS X E').inv ≫
      (smallEtaleModelDerivedEquivalence B S hS X).functor.map
        (smallEtaleDerivedDualOfHom B S hS X ψ) =
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.map ψ).op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) ≫
        (smallEtaleModelDerivedDualIso B S hS X E).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact smallEtaleModelDerivedDualIso_hom_naturality B S hS X ψ
  have s₂ : ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.map
          (smallEtaleDerivedDualOfHom B S hS X ψ)).op).app
          (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) ≫
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          (smallEtaleModelDerivedDualIso B S hS X E').inv.op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) =
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          (smallEtaleModelDerivedDualIso B S hS X E).inv.op).app
            (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) ≫
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
          (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).map
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.map ψ).op).app
              (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))).op).app
          (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2)) :=
    CategoryTheory.Functor.map_op_comm_of_comm ((RingedSite.derivedSheafHomBifunctor
      (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.obj
        (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))) n'
  refine (cancel_mono (RingedSite.derivedBidual (smallEtaleModelRingedSite B S hS X.1 X.2)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (smallEtaleModelRingedSite B S hS X.1 X.2))
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E'))).1 ?_
  simp only [Functor.map_comp]
  exact comp_bidual_chain
    (smallEtaleModelDerivedEquivalence_map_smallEtaleDerivedBidualIso_hom B S hS X E' hE')
    (smallEtaleModelDerivedEquivalence_map_smallEtaleDerivedBidualIso_hom B S hS X E hE)
    (RingedSite.comp_derivedBidual _ _ _)
    (CategoryTheory.comp_chain₂
      (smallEtaleModelDerivedDualIso_hom_naturality B S hS X
        (smallEtaleDerivedDualOfHom B S hS X ψ)) s₂)

/-- **Biduality for a system of perfect objects**, as an isomorphism of systems: for a functor
`M : Jᵒᵖ ⥤ D(𝒪_X)` with perfect values, the system of double duals `j ↦ (M_j^∨)^∨` is `M`. -/
def smallEtaleDerivedBidualSystemIso {J : Type*} [Category J]
    (M : Jᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : ∀ j, RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) (M.obj j)) :
    (M.rightOp ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))).op ⋙
      (smallEtaleDerivedSheafHom B S hS X).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) ≅ M :=
  NatIso.ofComponents (fun j => smallEtaleDerivedBidualIso B S hS X (M.obj j) (hM j))
    (fun {j j'} f => smallEtaleDerivedBidualIso_naturality B S hS X (M.map f) (hM j) (hM j'))

/-- **Stacks 0A0A for an algebraic space**: derived internal Hom out of a derived colimit is the
derived limit of the derived internal Homs out of its terms: if `K = hocolim Fₙ` in `D(𝒪_X)`, then
`R𝓗om(K, E) = R lim R𝓗om(Fₙ, E)`.  This is the statement on the equi-universe model, read
through the derived equivalence. -/
theorem isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit_of_hasProduct
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    [HasCoproduct F.obj]
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    [HasProduct fun n : ℕ => (F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E).obj (op n)]
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E)
      (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) := by
  have h₁ := RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'
    (smallEtaleModelRingedSite B S hS X.1 X.2)
    (F ⋙ (smallEtaleModelDerivedEquivalence B S hS X).functor)
    ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E)
    (hK.map (smallEtaleModelDerivedEquivalence B S hS X).functor)
  obtain ⟨_, h₂⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
    (smallEtaleModelDerivedEquivalence B S hS X).inverse _ _ h₁
  exact h₂

end AlgebraicGeometry.Space
