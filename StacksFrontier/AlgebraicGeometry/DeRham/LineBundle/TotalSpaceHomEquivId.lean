module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TautologicalSection
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceUniversal

/-!
# The universal point of the total space of a line bundle

Let `D` be a line-bundle situation: a morphism of schemes `X ⟶ S` together with an invertible
`𝒪_X`-module `L`. The functor of points of the total space `p : Tot(L) ⟶ X`,
`Stacks.LineBundle.Situation.totalSpaceHomEquiv`, writes a morphism `f : Y ⟶ Tot(L)` as a pair
consisting of `f ≫ p : Y ⟶ X` and a morphism of `𝒪_X`-modules `L ⟶ (f ≫ p)_* 𝒪_Y`. This file
identifies the second component: it is the degree-one inclusion

`L ⟶ p_* 𝒪_{Tot(L)}`

of `Stacks.LineBundle.Situation.genToPushforward` — the datum whose adjoint is the tautological
functional — pushed along `f`. In particular, at `f = 𝟙` the module morphism attached to the
identity of the total space *is* the degree-one inclusion: the identity is the universal point of
`Tot(L)`, and the tautological section is the fibre coordinate it records.

## Main results

* `Stacks.LineBundle.Situation.algebraPairEquiv_universalAlgebraMap`: **the module morphism
  attached to the universal algebra map of the relative spectrum is the degree-one inclusion
  `L ⟶ p_* 𝒪_{Tot(L)}`.** This is the heart of the file.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_snd`: **the module morphism attached to any
  `f : Y ⟶ Tot(L)` is the degree-one inclusion followed by the canonical map
  `p_* 𝒪_{Tot(L)} ⟶ (f ≫ p)_* 𝒪_Y`.** No restriction is placed on `Y` or `f`.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_id`: **the module morphism attached to the
  identity of the total space is the degree-one inclusion.**
* `Stacks.LineBundle.Situation.algebraSheafGen_val_app`: the degree-one inclusion into the module
  underlying the algebra sheaf, read on a local section: it is the degree-one homogeneous local
  section of `Sym(L)` that section determines.
* `Stacks.LineBundle.Situation.underlyingModuleIsoPushforward_hom_val_app`: Tag 01LX(3) read on
  underlying modules is, on local sections, the universal algebra map itself.

## Implementation notes

Everything is read on local sections, where the two sides of
`Stacks.LineBundle.Situation.algebraPairEquiv_universalAlgebraMap` become the same element of
`Γ(Tot(L), p^{-1}U)`, and the two places where that is not definitional are isolated as separate
statements.

The first is the degree-one inclusion. `Stacks.LineBundle.Situation.algebraSheafGen` is built from
the coproduct injection `Sym¹(L) ⟶ ∐_{n : ℕ} Symⁿ(L)` and
`Stacks.LineBundle.Situation.coprodIsoUnderlyingModule`, and the latter is a comparison of two
colimit cocones, so no amount of unfolding reaches the homogeneous local section
`Stacks.LineBundle.Situation.algebraSheafIncl`. The comparison is identified here componentwise:
`Stacks.sheafifyDirectSumIso` is a `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`, so
`CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv` computes it after the counit
of the sheafification adjunction, which is an isomorphism and so may be cancelled. What is left is
the naturality of that adjunction in both variables, applied to
`Stacks.sheafifyHomOfPresheafHom`, and that lands on the objectwise inclusion of a homogeneous
component — which is the homogeneous local section on the nose.

The second is Tag 01LX(3). `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso` ends in an
`CategoryTheory.eqToIso` transporting along
`Stacks.RelativeSpec.AlgebraSheaf.structureMap_comp_ringSheafMap`, an equality of two morphisms of
sheaves of rings. Restriction of scalars along either one has the same sections, so the transport
is the identity on sections; that statement is proved by generalizing the two morphisms and
substituting, which is what makes it provable at all — the equality being transported along is
between fixed terms, so it cannot be substituted where it occurs.

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

/-! ### The coproduct injections of a sheafified direct sum -/

section Sheafify

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The hom-equivalence of the sheafification adjunction for presheaves of modules is the
hom-equivalence it was built from. -/
private theorem sheafificationAdjunction_homEquiv (M₀ : PresheafOfModules.{u} R.obj)
    (M : SheafOfModules.{u} R) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv M₀ M =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := M₀) (F := M) :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M₀) M

/-- The morphism out of a sheafification determined by a morphism into a sheaf of modules is the
adjoint of that morphism. -/
private theorem sheafifyHomOfPresheafHom_eq {M : SheafOfModules.{u} R}
    {M₀ : PresheafOfModules.{u} R.obj} (c : M₀ ⟶ M.val) :
    Stacks.sheafifyHomOfPresheafHom c =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv M₀ M).symm c :=
  congrArg (fun e : ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M₀ ⟶ M) ≃
    (M₀ ⟶ (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((SheafOfModules.forget R).obj M)) => e.symm c)
    (sheafificationAdjunction_homEquiv M₀ M).symm

/-- Precomposing the morphism determined by `c` with a sheafified morphism is the morphism
determined by the composite: naturality of the sheafification adjunction in its source. -/
private theorem sheafifyHomOfPresheafHom_comp {M : SheafOfModules.{u} R}
    {M₀ M₁ : PresheafOfModules.{u} R.obj} (g : M₁ ⟶ M₀) (c : M₀ ⟶ M.val) :
    Stacks.sheafifyHomOfPresheafHom (g ≫ c) =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map g ≫ Stacks.sheafifyHomOfPresheafHom c :=
  (sheafifyHomOfPresheafHom_eq (g ≫ c)).trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
        (Y := M) g c).trans
      (congrArg (fun z => (PresheafOfModules.sheafification (𝟙 R.obj)).map g ≫ z)
        (sheafifyHomOfPresheafHom_eq c).symm))

/-- The counit of the sheafification adjunction followed by a morphism of sheaves of modules is
the morphism determined by that morphism: naturality in the target, together with the triangle
identity. -/
private theorem counit_comp {M N : SheafOfModules.{u} R} (t : N ⟶ M) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N ≫ t =
      Stacks.sheafifyHomOfPresheafHom t.val :=
  ((sheafifyHomOfPresheafHom_eq t.val).trans
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_counit N.val M t.val).trans
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit_naturality t))).symm

/-- After the counit of the sheafification adjunction, the coproduct injection of a family of
sheaves of modules, read through `Stacks.sheafifyDirectSumIso`, is the sheafification of the
objectwise inclusion of the corresponding summand. -/
private theorem counit_comp_sigma_ι {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{u} R)
    [HasCoproduct N] (n : ι) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N n) ≫
        Sigma.ι N n ≫ (Stacks.sheafifyDirectSumIso N).inv =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
        (Stacks.inclHom (fun i => (N i).val) n) :=
  (Category.assoc _ _ _).symm.trans
    (IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
        (Stacks.directSumIsColimit fun i => (N i).val))
      ((IsColimit.precomposeHomEquiv (Stacks.sheafificationDirectSumComponentIso N)
          (colimit.cocone (Discrete.functor N))).symm
        (colimit.isColimit (Discrete.functor N))) (⟨n⟩ : Discrete ι))

/-- **The coproduct injection of a family of sheaves of modules, read through
`Stacks.sheafifyDirectSumIso` and a morphism `c` out of the objectwise direct sum, is `c`
restricted to the corresponding summand.** -/
private theorem sigma_ι_comp_sheafifyHomOfPresheafHom {ι : Type} [DecidableEq ι]
    (N : ι → SheafOfModules.{u} R) [HasCoproduct N] {M : SheafOfModules.{u} R}
    (c : Stacks.directSum (fun i => (N i).val) ⟶ M.val) (n : ι) :
    Sigma.ι N n ≫ (Stacks.sheafifyDirectSumIso N).inv ≫ Stacks.sheafifyHomOfPresheafHom c =
      (⟨Stacks.inclHom (fun i => (N i).val) n ≫ c⟩ : N n ⟶ M) := by
  have : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N n)) :=
    ((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).app (N n)).isIso_hom
  refine (cancel_epi
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N n))).mp ?_
  refine Eq.trans ?_ (counit_comp (⟨Stacks.inclHom (fun i => (N i).val) n ≫ c⟩ : N n ⟶ M)).symm
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N n)),
    counit_comp_sigma_ι]
  exact (sheafifyHomOfPresheafHom_comp _ _).symm

end Sheafify

/-! ### The homogeneous summands of the module underlying an ungraded algebra sheaf -/

section Coprod

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (TopologicalSpace.Opens X)ᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U), HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (hzero : ∀ n : ℤ, n < 0 → Limits.IsZero (A.piece n))

/-- **The coproduct injection of the homogeneous piece of degree `n`, read through the
identification of the module underlying the ungraded algebra sheaf with the coproduct of the
homogeneous pieces, is the objectwise inclusion of that summand.** -/
private theorem sigma_ι_comp_coprodIsoUnderlyingModule (n : ℕ) :
    Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n ≫ (coprodIsoUnderlyingModule X A hA hzero).hom =
      (⟨Stacks.inclHom (fun m : ℕ => (A.piece (m : ℤ)).val) n ≫ coprodDirectSumHom X A hA⟩ :
        A.piece (n : ℤ) ⟶ AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA)) :=
  sigma_ι_comp_sheafifyHomOfPresheafHom _ _ n

/-- **A homogeneous local section of degree `n`, injected into the coproduct of the homogeneous
pieces and read through the identification of that coproduct with the module underlying the
ungraded algebra sheaf, is that section viewed in the sections of the algebra sheaf.** -/
private theorem sigma_ι_comp_coprodIsoUnderlyingModule_app (n : ℕ) (U : X.Opens)
    (y : (A.piece (n : ℤ)).val.obj (op U)) :
    (((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n ≫
        (coprodIsoUnderlyingModule X A hA hzero).hom).val.app (op U))).hom y =
      ungradedAlgebraSheafIncl X A hA (n : ℤ) U y := by
  have h : Stacks.inclHom (fun m : ℕ => (A.piece (m : ℤ)).val) n ≫ coprodDirectSumHom X A hA =
      Stacks.inclHom (fun m : ℤ => (A.piece m).val) (n : ℤ) ≫ ungradedDirectSumHom X A hA := by
    rw [coprodDirectSumHom, ← Category.assoc, Stacks.directSumNatToInt,
      Stacks.inclHom_directSumDesc]
  refine Eq.trans (congrArg (fun k : A.piece (n : ℤ) ⟶
      AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA) =>
    (k.val.app (op U)).hom y) (sigma_ι_comp_coprodIsoUnderlyingModule X A hA hzero n)) ?_
  exact congrArg (fun k : (A.piece (n : ℤ)).val ⟶
      (AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA)).val =>
    (k.app (op U)).hom y) h

end Coprod

/-! ### The underlying module of an isomorphism of algebra sheaves, on sections -/

section UnderlyingModuleIso

/-- Restriction of scalars along two equal morphisms of sheaves of rings has the same sections, so
the transport between them is the identity on sections. The two morphisms are generalized so that
the equality can be substituted. -/
private theorem restrictScalars_eqToHom_val_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (N : SheafOfModules.{u} R')
    {α β : R ⟶ R'} (p : α = β) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars β).obj N).val.obj U) :
    ((eqToHom (congrArg (fun γ : R ⟶ R' =>
          (SheafOfModules.restrictScalars γ).obj N) p.symm)).val.app U).hom x = x := by
  subst p
  rfl

/-- **The inverse of the isomorphism of underlying modules attached to an isomorphism of algebra
sheaves is, on local sections, the inverse isomorphism of algebra sheaves.** -/
private theorem underlyingModuleIso_inv_val_app {X : Scheme.{u}} {A A' : AlgebraSheaf X}
    (e : A ≅ A') (U : (X.Opens)ᵒᵖ) (x : (AlgebraSheaf.underlyingModule A').val.obj U) :
    ((AlgebraSheaf.underlyingModuleIso e).inv.val.app U).hom x =
      (e.inv.right.hom.app U).hom x :=
  congrArg (fun z : ((SheafOfModules.restrictScalars (AlgebraSheaf.structureMap A)).obj
      ((SheafOfModules.restrictScalars (AlgebraSheaf.ringSheafMap e.hom)).obj
        (SheafOfModules.unit (AlgebraSheaf.ringSheaf A')))).val.obj U =>
    (e.inv.right.hom.app U).hom z)
    (restrictScalars_eqToHom_val_app _ (AlgebraSheaf.structureMap_comp_ringSheafMap e.hom) U x)

end UnderlyingModuleIso

/-! ### The universal point of the total space -/

variable (D : Situation.{u})

/-- **The degree-one inclusion `L ⟶ Sym(L)` of a line bundle, on a local section of `L`**: it is
the degree-one homogeneous local section of `Sym(L)` that section determines, viewed in the
sections of the algebra sheaf. -/
theorem Situation.algebraSheafGen_val_app (U : D.X.Opens) (s : D.L.val.obj (op U)) :
    (D.algebraSheafGen.val.app (op U)).hom s =
      D.algebraSheafIncl 1 U (D.symmetricAlgebraGen.val.app (op U) s) :=
  sigma_ι_comp_coprodIsoUnderlyingModule_app D.X D.symmetricAlgebra D.symmetricAlgebra_mul_comm
    D.isZero_symmetricAlgebra_piece 1 U (D.symmetricAlgebraGen.val.app (op U) s)

/-- **Tag 01LX(3) for the total space of a line bundle, read on underlying modules and on local
sections, is the universal algebra map of the relative spectrum.** -/
theorem Situation.underlyingModuleIsoPushforward_hom_val_app (U : D.X.Opens)
    (x : (AlgebraSheaf.underlyingModule D.algebraSheaf).val.obj (op U)) :
    (D.underlyingModuleIsoPushforward.hom.val.app (op U)).hom x =
      ((pushforwardAlgebraIso D.algebraSheaf).inv.right.hom.app (op U)).hom x :=
  underlyingModuleIso_inv_val_app (pushforwardAlgebraIso D.algebraSheaf) (op U) x

/-- **The module morphism attached to the universal algebra map of the relative spectrum is the
degree-one inclusion `L ⟶ p_* 𝒪_{Tot(L)}`.** On a local section of `L` both sides are the
degree-one homogeneous local section of `Sym(L)` it determines, read through Tag 01LX(3). -/
theorem Situation.algebraPairEquiv_universalAlgebraMap :
    D.algebraPairEquiv D.totalSpaceToBase (universalAlgebraMap D.relativeSpecSituation) =
      D.genToPushforward := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  obtain ⟨U⟩ := W
  refine Eq.trans ?_ (D.underlyingModuleIsoPushforward_hom_val_app U
    ((D.algebraSheafGen.val.app (op U)).hom s)).symm
  exact congrArg
    (fun z => ((pushforwardAlgebraIso D.algebraSheaf).inv.right.hom.app (op U)).hom z)
    (D.algebraSheafGen_val_app U s).symm

/-- **The module morphism attached to a morphism `f : Y ⟶ Tot(L)` into the total space of a line
bundle is the degree-one inclusion `L ⟶ p_* 𝒪_{Tot(L)}` followed by the canonical map
`p_* 𝒪_{Tot(L)} ⟶ (f ≫ p)_* 𝒪_Y`.** No restriction is placed on `Y` or `f`. -/
theorem Situation.totalSpaceHomEquiv_snd {Y : Scheme.{u}} (f : Y ⟶ D.totalSpace) :
    (D.totalSpaceHomEquiv Y f).2 =
      D.genToPushforward ≫ AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMapAux D.totalSpaceToBase f) :=
  (D.algebraPairEquiv_comp f D.totalSpaceToBase
      (universalAlgebraMap D.relativeSpecSituation)).trans
    (congrArg (fun z => z ≫ AlgebraSheaf.underlyingModuleMap
      (pushforwardAlgebraMapAux D.totalSpaceToBase f))
      D.algebraPairEquiv_universalAlgebraMap)

/-- **The module morphism attached to the identity of the total space of a line bundle is the
degree-one inclusion `L ⟶ p_* 𝒪_{Tot(L)}`**: the identity is the universal point of `Tot(L)`, and
the functional it records on each fibre is evaluation against that fibre's point. -/
theorem Situation.totalSpaceHomEquiv_id :
    (D.totalSpaceHomEquiv D.totalSpace (𝟙 D.totalSpace)).2 = D.genToPushforward :=
  D.algebraPairEquiv_universalAlgebraMap

end Stacks.LineBundle

end
