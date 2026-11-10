module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekConstantCopower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat constructibility of the generators of a shriek presentation

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site. Tag 03S8 asserts that
for `j : U ⟶ X` étale with `U` quasi-compact and quasi-separated the sheaf
`j_{U!}\underline{\Lambda}_U` of `Λ`-modules is constructible, which is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`. The source leaves unstated
that this sheaf is moreover *flat* — constructible flat in the sense of
`AlgebraicGeometry.IsConstructibleFlatModuleSheaf`, i.e. stratumwise locally constant with finite
*projective* values rather than merely finitely generated ones. This file proves that refinement,
and the closure of flat constructibility under finite direct sums.

The refinement is Tag 03S8 for modules with `Module.Projective` adjoined to `ModuleCat.isFG`:
on a stratum the constant value of the module sheaf is the free module `Λ^{(E)}` on the finite
constant value `E` of the sheaf of sets `h_U^#`, and a finite free module is finite projective.

## Main definitions

* `Stacks.ConstantSheaf.IsConstantFiniteProjectiveOver` and
  `Stacks.ConstantSheaf.finProjTrivSieve`: the condition on one member of a trivializing covering
  in `Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant`, and the sieve of arrows whose
  source satisfies it.

## Main results

* `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_free`: the free
  module sheaf on a finite locally constant sheaf of sets is locally constant with finite
  projective values, on any site.
* `AlgebraicGeometry.isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback`: that condition
  survives inverse image along an arbitrary morphism of a big étale site, in particular along a
  stratum immersion.
* `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_sigma`: and is closed under finite
  direct sums.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma`: **flat constructibility is closed
  under finite direct sums**, for an arbitrary ring in an arbitrary module universe.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_composeAndSheafify_copower`: flat
  constructibility transfers across the copower module sheaf functor.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_moduleShriekConstant`: **the flat refinement
  of Tag 03S8 for sheaves of modules**, and
  `AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant`, the finite
  direct sum of such generators at affine objects. Both hold for a ring `Λ : Type r` in a
  universe of its own, over a quasi-compact and quasi-separated scheme.

## Implementation notes

The closure under finite direct sums is proved through the trivializing sieve rather than by
intersecting coverings by hand: `Stacks.ConstantSheaf.finProjTrivSieve` is a sieve because
`Stacks.ConstantSheaf.IsConstantFiniteProjectiveOver` is a condition on the *source* of an arrow,
a finite intersection of covering sieves covers
(`Stacks.Sheafification.finsetInf_covering`), and over a common member all summands are constant,
so the direct sum is constant with value their direct sum — both the constant sheaf functor on a
slice site and restriction to that slice being left adjoints, hence preserving the coproduct.
This is the module analogue of the sheaf-of-sets argument of
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sigma`.

The generators are compared with the *copower* module sheaf
`ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ))` rather than with the free module
sheaf `ModuleCat.free Λ`, and that is what lets the coefficient ring live in a universe `r` of
its own. `ModuleCat.free Λ` has source `Type r ⥤ ModuleCat.{r} Λ` and so ties the module universe
to the ring universe, whereas `ModuleCat.copower M : Type w ⥤ ModuleCat.{w} Λ` leaves the ring
universe free; the two functors are the same `E ↦ Λ^{(E)}` wherever both are defined. The copower
takes its sheaf of sets in the module universe `max (u + 1) r`, where
`CategoryTheory.Sheaf.sheafifiedYoneda` does not live, so part (1) of Tag 03S8 is used in the form
`AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`, for the
universe-polymorphic sheafified representable `CategoryTheory.Sheaf.sheafifiedUliftYoneda`. See
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekConstantCopower` and
`StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseLift`.

`Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_free` is the
corresponding statement for the free module sheaf, the case `r = u + 1`.

Everything else in this file is universe polymorphic:
`AlgebraicGeometry.IsConstructibleFlatModuleSheaf` stays stated at `[Ring Λ]` in an arbitrary
module universe, and the closure results above are proved there.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u c r

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type w) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, HasWeakSheafify (J.over V) (Type w)]
  [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G]

omit [HasWeakSheafify J (Type w)] in
/-- **The free module sheaf on a finite locally constant sheaf of sets is locally constant with
finite projective values.** This is the flat refinement of
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_composeAndSheafify_free`. -/
public theorem isFiniteProjectiveLocallyConstant_composeAndSheafify_free
    (F : Sheaf J (Type w)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteProjectiveLocallyConstant R J
      ((Sheaf.composeAndSheafify J (ModuleCat.free R)).obj F) := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  refine ⟨(ModuleCat.free R).obj E, ?_, ?_, ⟨?_⟩⟩
  · change Module.Finite R (E →₀ R)
    infer_instance
  · change Module.Projective R (E →₀ R)
    infer_instance
  · exact ((Sheaf.constantSheafComposeAndSheafifyFreeIso (J.over (V i)) R
        Over.mkIdTerminal).app E).symm ≪≫
      (Sheaf.composeAndSheafify (J.over (V i)) (ModuleCat.free R)).mapIso e ≪≫
      ((Sheaf.composeAndSheafifyFreeOverPullbackIso J R (V i)).app F).symm

section Sigma

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (R : Type r) [Ring R]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G]
  [∀ (U V : C) (f : V ⟶ U) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.map f).op.HasPointwiseRightKanExtension G]

/-- `F` becomes, after restriction to the slice site `C/V`, the constant sheaf attached to a
finite projective module. This is the condition on one member of the covering family in
`Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant`. -/
public def IsConstantFiniteProjectiveOver (V : C) (F : Sheaf J (ModuleCat.{w} R)) : Prop :=
  ∃ E : ModuleCat.{w} R, Module.Finite R E ∧ Module.Projective R E ∧
    Nonempty ((constantSheaf (J.over V) (ModuleCat.{w} R)).obj E ≅
      (J.overPullback (ModuleCat.{w} R) V).obj F)

omit [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G] in
/-- Local triviality with finite projective value passes to every object lying over a
trivializing one. -/
public theorem IsConstantFiniteProjectiveOver.restrict {U V : C} (g : V ⟶ U)
    {F : Sheaf J (ModuleCat.{w} R)} (h : IsConstantFiniteProjectiveOver J R U F) :
    IsConstantFiniteProjectiveOver J R V F := by
  obtain ⟨E, hfin, hproj, ⟨φ⟩⟩ := h
  exact ⟨E, hfin, hproj, ⟨(mapPullbackConstantSheafIso J (ModuleCat.{w} R) g).app E ≪≫
    (J.overMapPullback (ModuleCat.{w} R) g).mapIso φ⟩⟩

/-- The sieve of arrows over whose source `F` becomes constant with finite projective value. -/
public def finProjTrivSieve (F : Sheaf J (ModuleCat.{w} R)) (U : C) : Sieve U where
  arrows V _ := IsConstantFiniteProjectiveOver J R V F
  downward_closed h g := h.restrict J R g

omit [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G] in
/-- Local constancy with finite projective values is exactly: the trivializing sieve covers every
object. -/
public theorem isFiniteProjectiveLocallyConstant_iff_trivSieve_mem
    (F : Sheaf J (ModuleCat.{w} R)) :
    IsFiniteProjectiveLocallyConstant R J F ↔ ∀ U : C, finProjTrivSieve J R F U ∈ J U := by
  constructor
  · intro hF U
    obtain ⟨I, X, f, hf, h⟩ := hF U
    refine J.superset_covering ?_ hf
    rw [Sieve.generate_le_iff]
    rintro Y p ⟨i⟩
    exact h i
  · intro hF U
    obtain ⟨I, X, f, hXf⟩ := Sieve.exists_eq_ofArrows (finProjTrivSieve J R F U)
    exact ⟨I, X, f, hXf ▸ hF U, fun i ↦
      (hXf ▸ Sieve.ofArrows_mk X f i : finProjTrivSieve J R F U (f i))⟩

omit [∀ (V : C) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.forget V).op.HasPointwiseRightKanExtension G]
  [∀ (U V : C) (f : V ⟶ U) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.map f).op.HasPointwiseRightKanExtension G] in
/-- The constant sheaf functor on a slice site preserves the coproducts indexed by any
`ι : Type`: it is the left adjoint of evaluation at the terminal object `𝟙 V` of `C/V`. -/
public theorem preservesColimitsOfShape_constantSheaf_over (V : C) (ι : Type) :
    PreservesColimitsOfShape (Discrete ι)
      (constantSheaf (J.over V) (ModuleCat.{w} R)) := by
  have : PreservesColimitsOfSize.{0, 0} (constantSheaf (J.over V) (ModuleCat.{w} R)) :=
    (constantSheafAdj (J.over V) (ModuleCat.{w} R)
      (Over.mkIdTerminal (X := V))).leftAdjoint_preservesColimits
  infer_instance

omit [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ (U V : C) (f : V ⟶ U) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.map f).op.HasPointwiseRightKanExtension G] in
/-- Restriction to a slice site preserves the coproducts indexed by any `ι : Type`: it is
the left adjoint of `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, `Over.forget V` being
cocontinuous. -/
@[ega "0 4.3.2" "partial"]
public theorem preservesColimitsOfShape_overPullback (V : C) (ι : Type) :
    PreservesColimitsOfShape (Discrete ι) (J.overPullback (ModuleCat.{w} R) V) := by
  have : PreservesColimitsOfSize.{0, 0} (J.overPullback (ModuleCat.{w} R) V) :=
    ((Over.forget V).sheafAdjunctionCocontinuous (ModuleCat.{w} R)
      (J.over V) J).leftAdjoint_preservesColimits
  infer_instance

omit [∀ (U V : C) (f : V ⟶ U) (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
    (Over.map f).op.HasPointwiseRightKanExtension G] in
/-- **A finite direct sum of sheaves constant with finite projective value over `V` is constant
with finite projective value over `V`.** -/
public theorem IsConstantFiniteProjectiveOver.sigma {ι : Type} [Finite ι] {V : C}
    {F : ι → Sheaf J (ModuleCat.{w} R)} [Limits.HasCoproduct F]
    (h : ∀ i, IsConstantFiniteProjectiveOver J R V (F i)) :
    IsConstantFiniteProjectiveOver J R V (∐ F) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose E hfin hproj hiso using h
  have : Module.Finite R (DirectSum ι (fun i ↦ (E i : Type w))) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype R ι (fun i ↦ (E i : Type w))).symm
  have : Module.Projective R (DirectSum ι (fun i ↦ (E i : Type w))) := inferInstance
  have : Module.Finite R (∐ E : ModuleCat.{w} R) :=
    Module.Finite.equiv (ModuleCat.coprodIsoDirectSum E).toLinearEquiv.symm
  have : Module.Projective R (∐ E : ModuleCat.{w} R) :=
    Module.Projective.of_equiv' (ModuleCat.coprodIsoDirectSum E).toLinearEquiv.symm
  have := preservesColimitsOfShape_constantSheaf_over J R V ι
  have := preservesColimitsOfShape_overPullback J R V ι
  let e : Discrete.functor E ⋙ constantSheaf (J.over V) (ModuleCat.{w} R) ≅
      Discrete.functor F ⋙ J.overPullback (ModuleCat.{w} R) V :=
    Discrete.natIso (fun i ↦ (hiso i.as).some)
  exact ⟨∐ E, inferInstance, inferInstance,
    ⟨preservesColimitIso (constantSheaf (J.over V) (ModuleCat.{w} R))
        (Discrete.functor E) ≪≫
      HasColimit.isoOfNatIso e ≪≫
      (preservesColimitIso (J.overPullback (ModuleCat.{w} R) V)
        (Discrete.functor F)).symm⟩⟩

/-- **A finite direct sum of sheaves of modules locally constant with finite projective values is
locally constant with finite projective values.** -/
public theorem isFiniteProjectiveLocallyConstant_sigma {ι : Type} [Finite ι]
    (F : ι → Sheaf J (ModuleCat.{w} R)) [HasCoproduct F]
    (h : ∀ i, IsFiniteProjectiveLocallyConstant R J (F i)) :
    IsFiniteProjectiveLocallyConstant R J (∐ F) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [isFiniteProjectiveLocallyConstant_iff_trivSieve_mem]
  intro U
  have hcov : (Finset.univ.inf fun i ↦ finProjTrivSieve J R (F i) U) ∈ J U :=
    Stacks.Sheafification.finsetInf_covering J Finset.univ _
      (fun i ↦ ((isFiniteProjectiveLocallyConstant_iff_trivSieve_mem J R (F i)).mp (h i)) U)
  refine J.superset_covering (fun Y p hp ↦ ?_) hcov
  exact IsConstantFiniteProjectiveOver.sigma J R
    (fun i ↦ (Finset.inf_le (Finset.mem_univ i) :
      _ ≤ finProjTrivSieve J R (F i) U) p hp)

end Sigma

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

/-- **Local constancy with finite projective values survives inverse image along any morphism of
a big étale site.** This is the flat refinement of
`AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback`. -/
public theorem isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback (B : BigEtaleSite.{u})
    (R : Type r) [Ring R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
      HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} R)]
    {S T : B.Scheme} (g : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} R))
    (hH : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant R
      (SmallEtale.topology B S.obj S.property) H) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant R
      (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj H) := by
  intro U
  obtain ⟨I, W, f, hcov, hc⟩ :=
    exists_trivializing_cover_smallEtaleSheafPullback B (ModuleCat.{w} R) g H
      (fun E ↦ Module.Finite R E ∧ Module.Projective R E)
      (fun V ↦ by
        obtain ⟨I, V', f', hcov', hc'⟩ := hH V
        exact ⟨I, V', f', hcov', fun i ↦ by
          obtain ⟨E, hfin, hproj, he⟩ := hc' i
          exact ⟨E, ⟨hfin, hproj⟩, he⟩⟩) U
  refine ⟨I, W, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, ⟨hfin, hproj⟩, he⟩ := hc i
  exact ⟨E, hfin, hproj, he⟩

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **Flat constructibility is closed under finite direct sums.** The ring `Λ` need not be
commutative or Noetherian, and nothing is assumed of `X`. -/
public theorem isConstructibleFlatModuleSheaf_sigma (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property)
        (G : (Over V)ᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Over.forget V).op.HasPointwiseRightKanExtension G]
    [∀ (T : B.Scheme) (V V' : SmallEtale B T.obj T.property) (f : V' ⟶ V)
        (G : (Over V')ᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Over.map f).op.HasPointwiseRightKanExtension G]
    [∀ T : B.Scheme,
      HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)]
    {n : ℕ} (F : Fin n → Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : ∀ j, IsConstructibleFlatModuleSheaf B X Λ (F j)) :
    IsConstructibleFlatModuleSheaf B X Λ (∐ F) := by
  intro U
  obtain ⟨s, hs⟩ := exists_stratification_isStratifiedSheaf_forall B X
    (fun T H ↦ Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B T.obj T.property) H)
    (fun _ _ _ e h ↦ Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ e h)
    (fun _ _ g _ H h ↦ isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ g H h)
    hF U
  refine ⟨s, fun k ↦ ?_⟩
  set G := (smallEtaleBaseChange B (s.inclusion k)).sheafPullback (ModuleCat.{w} Λ)
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (s.piece k).obj (s.piece k).property)
  have : PreservesColimitsOfSize.{0, 0} G :=
    ((smallEtaleBaseChange B (s.inclusion k)).sheafAdjunctionContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece k).obj
        (s.piece k).property)).leftAdjoint_preservesColimits
  have hsum := Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_sigma
    (SmallEtale.topology B (s.piece k).obj (s.piece k).property) Λ
    (fun j ↦ G.obj (F j)) (fun j ↦ hs k j)
  refine Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ ?_ hsum
  let e : Discrete.functor F ⋙ G ≅ Discrete.functor fun j ↦ G.obj (F j) :=
    Discrete.natIso fun _ ↦ Iso.refl _
  exact (preservesColimitIso G (Discrete.functor F) ≪≫ HasColimit.isoOfNatIso e).symm

section Generator

attribute [local instance] isRightAdjoint_sheafPushforwardContinuous_type_uliftSmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

/-- **Flat constructibility transfers across the copower module sheaf functor.** The copower
module sheaf by a finite free `Λ`-module on a constructible sheaf of sets on `X_étale` is a flat
constructible sheaf of `Λ`-modules. This is the flat refinement of
`AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_copower`. -/
public theorem isConstructibleFlatModuleSheaf_composeAndSheafify_copower
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] [Module.Free Λ M]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type max (u + 1) r))
    (hF : IsConstructibleFiniteSheaf B X F) :
    IsConstructibleFlatModuleSheaf B X Λ
      ((Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
        (ModuleCat.copower M)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  refine Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
    ((Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso
      (SmallEtale.topology B X.obj X.property) M
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (smallEtaleBaseChange B (s.inclusion i))).app F).symm ?_
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_composeAndSheafify_copower _ Λ M _
    (hs i)

/-- **The flat refinement of Stacks 03S8 for sheaves of modules.** For `U` a quasi-compact
quasi-separated object of the small étale site of a quasi-compact quasi-separated scheme `X`, and
`Λ` a commutative ring in an arbitrary universe `r`, the extension by zero
`j_{U!}\underline{\Lambda}_U` of the constant free rank-one module sheaf is a *flat*
constructible sheaf of `Λ`-modules in `ModuleCat.{max (u + 1) r} Λ`: on each stratum of the
stratification of Stacks 03S0 it is locally constant with finite free, hence finite projective,
values.

By `AlgebraicGeometry.moduleShriekConstantIsoCopower` this sheaf is the copower module sheaf by
the free rank-one module on the sheaf `h_U^#` of sets, which is constructible as a sheaf of sets
in the module universe by part (1) of Stacks 03S8,
`AlgebraicGeometry.isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs`.

No `@[stacks 03S8]` attribute is attached: the source asserts constructibility of
`j_{U!}\underline{\Lambda}_U`, which is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant` and carries the tag, and
leaves its flatness unstated. This is the extra statement, not a second proof of the tag. -/
public theorem isConstructibleFlatModuleSheaf_moduleShriekConstant
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleFlatModuleSheaf B X Λ (moduleShriekConstant.{u, r, r} B X Λ U) := by
  intro V
  obtain ⟨s, hs⟩ := isConstructibleFlatModuleSheaf_composeAndSheafify_copower B X Λ
    (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)) _
    (isConstructibleFiniteSheaf_sheafifiedUliftYoneda_of_qcqs.{r} B X U) V
  refine ⟨s, fun i ↦ ?_⟩
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso
        (moduleShriekConstantIsoCopower B X Λ U).symm) (hs i)

/-- **A finite direct sum of extensions by zero of constant free rank-one module sheaves at
affine objects is flat constructible**, for a commutative ring in an arbitrary universe. -/
public theorem isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {n : ℕ}
    (U : Fin n → SmallEtale B X.obj X.property)
    (hU : ∀ j, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j))) :
    IsConstructibleFlatModuleSheaf B X Λ
      (∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j)) := by
  have : ∀ T : B.Scheme,
      HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ) :=
    fun T ↦ SmallEtale.hasSheafify_moduleCat.{u, r, r} B T Λ
  refine isConstructibleFlatModuleSheaf_sigma B X Λ _ fun j ↦ ?_
  have hA : IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j)) := hU j
  have hc : CompactSpace (U j).obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U j)))
  have hq : QuasiSeparatedSpace (U j).obj.left.obj :=
    inferInstanceAs (QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U j)))
  exact isConstructibleFlatModuleSheaf_moduleShriekConstant B X Λ (U j)

end Generator

end AlgebraicGeometry

end
