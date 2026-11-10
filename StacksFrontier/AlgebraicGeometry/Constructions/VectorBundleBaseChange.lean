module

public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.SymmetricAlgebraLiftCompat
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Reduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the vector bundle of a module

Let `g : T ⟶ S` be a morphism of schemes and `M` a quasi-coherent `𝒪_S`-module, with vector
bundle `𝐕(M) = Spec_S(Sym(M))`. Then

  `𝐕(M) ×_S T = 𝐕(g^* M)`

as schemes over `T`. By Stacks 01LX (2) the left side is the relative spectrum of the pulled-back
algebra `g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T`, so the statement is the algebra form of Stacks 01CI:
`g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T = Sym(g^* M)`.

That identification is proved from the two universal properties involved. A morphism of
algebra sheaves out of `g⁻¹ Sym(M) ⊗ 𝒪_T` is a morphism `Sym(M) ⟶ g_*(-)` of `𝒪_S`-algebras, and
a morphism of algebra sheaves out of `Sym(N)` is a morphism of modules out of `N`; the two
comparison maps are built from these and the adjunction `g^* ⊣ g_*` for modules, and they are
mutually inverse because both universal properties come with uniqueness.

## Main definitions

* `Stacks.SymAlgSheaf.homPiece`, `Stacks.SymAlgSheaf.gradedHom` — the degreewise components of a
  morphism of algebra sheaves out of `Sym(F)`.
* `Stacks.SymAlgSheaf.symmetricAlgebraSheafι` — the generator `F ⟶ Sym(F)` as a morphism of
  modules into the module underlying the algebra sheaf `Sym(F)`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafPullbackIso` — Stacks 01CI for the
  algebra sheaf: `g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T ≅ Sym(g^* M)`.
* `AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackAlgebraIso` — the pushed-forward
  structure sheaf of `𝐕(M) ×_S T ⟶ T` is `Sym(g^* M)`.
* `AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackOverIso` — `𝐕(M) ×_S T ≅ 𝐕(g^* M)` as
  schemes over `T`, and `AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackIso` the same on
  underlying schemes.

## Main results

* `Stacks.SymAlgSheaf.eq_algebraLift` and `Stacks.SymAlgSheaf.algebraHom_ext` — **uniqueness in
  the ungraded universal property of `Sym(F)`**: a morphism of algebra sheaves out of `Sym(F)` is
  the lift `Stacks.SymAlgSheaf.algebraLift` of its restriction to the generator.
* `AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackIso_hom_vectorBundleToBase` — the
  identification is one of schemes over `T`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafPullbackIso_hom_naturality` and
  `AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackOverIso_hom_naturality` — both
  identifications are natural in the module: the second intertwines the base change of
  `𝐕(f)` with `𝐕(g^* f)`.

## Implementation notes

Uniqueness out of `Sym(F)` is uniqueness in the *graded* universal property of `Sym(F)`, applied
to the degreewise components of the morphism, which form a unital homomorphism into the
degenerately graded `Stacks.SymAlgSheaf.constGraded`; the passage to the ungraded realization is
that a morphism out of a sheafification is determined by its composite with the unit.

The module underlying the direct image of an algebra sheaf is, on the nose, the direct image of
its underlying module (`underlyingModuleMap_algebraPushforward_map` is `rfl`), which is what lets
the module adjunction `g^* ⊣ g_*` be composed with the algebra adjunction.

The identification `𝐕(M) ×_S T ≅ 𝐕(g^* M)` is built from the identification of algebras by
`AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso`, whose algebra map is known, rather than
from `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`, whose algebra map is not
characterized; this is what makes its naturality in the module provable, by comparing algebra
maps (`Stacks.AffineAlgebraEquivalence.eq_of_pushforwardAlgebraMap_eq`).

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SymAlgSheaf

variable {X : Scheme.{u}} (𝒜 : X.QuasicoherentAlgebra) (F : SheafOfModules.{u} X.ringCatSheaf)

/-- The degree-`n` component of a morphism of algebra sheaves `Ψ : Sym(F) ⟶ 𝒜`, as a morphism of
sheaves of modules `Symⁿ(F) ⟶ 𝒜`: a homogeneous local section is viewed in the ungraded
realization and then mapped by `Ψ`. -/
def homPiece (Ψ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜)
    (n : ℤ) : (Scheme.Modules.symmetricAlgebra X F).piece n ⟶
      Scheme.QuasicoherentAlgebra.underlyingModule 𝒜 :=
  show SheafOfModules.Hom _ _ from
  { val :=
    { app := fun W => ConcreteCategory.ofHom
        (C := ModuleCat (X.ringCatSheaf.obj.obj W))
        { toFun := fun x => (Ψ.right.hom.app W).hom
            ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n x)
          map_add' := fun x y => by
            refine (congrArg (Ψ.right.hom.app W).hom
              (SheafOfModules.GradedAlgebra.ungradedIncl_add _ n W x y)).trans ?_
            exact map_add (Ψ.right.hom.app W).hom _ _
          map_smul' := fun r x => by
            change (Ψ.right.hom.app W).hom
                ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n (r • x)) =
              (𝒜.hom.hom.app W).hom r * (Ψ.right.hom.app W).hom
                ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n x)
            refine (congrArg (Ψ.right.hom.app W).hom
              (SheafOfModules.GradedAlgebra.ungradedIncl_smul _ n W r x)).trans ?_
            refine (map_mul (Ψ.right.hom.app W).hom _ _).trans ?_
            exact congrArg (· * _) (congrArg (fun φ => (φ.hom.app W).hom r) (Under.w Ψ)) }
      naturality := fun {W W'} f => by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun x => ?_
        change (Ψ.right.hom.app W').hom
            ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n
              (((Scheme.Modules.symmetricAlgebra X F).piece n).val.map f x)) =
          (𝒜.right.obj.map f).hom ((Ψ.right.hom.app W).hom
            ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n x))
        refine (congrArg (Ψ.right.hom.app W').hom
          (SheafOfModules.GradedAlgebra.ungradedIncl_naturality _ f n x).symm).trans ?_
        exact congrArg (fun φ => CommRingCat.Hom.hom φ
          ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n x))
          (Ψ.right.hom.naturality f) } }

/-- On sections, the degree-`n` component of `Ψ` is `Ψ` on the ungraded image of a homogeneous
section. -/
theorem homPiece_apply
    (Ψ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜) (n : ℤ)
    (W : (Opens ↥X)ᵒᵖ) (x : ((Scheme.Modules.symmetricAlgebra X F).piece n).val.obj W) :
    (homPiece 𝒜 F Ψ n).val.app W x =
      (Ψ.right.hom.app W).hom ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl n x) :=
  rfl

/-- A morphism of algebra sheaves `Ψ : Sym(F) ⟶ 𝒜`, read degreewise as a unital homomorphism of
sheaves of graded algebras into `Stacks.SymAlgSheaf.constGraded 𝒜`. -/
def gradedHom (Ψ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜) :
    SheafOfModules.GradedAlgebra.UnitalHom (Scheme.Modules.symmetricAlgebra X F)
      (constGraded 𝒜) where
  app n := homPiece 𝒜 F Ψ n
  map_mul i j W x y := by
    change (Ψ.right.hom.app W).hom
        ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl (i + j)
          (((Scheme.Modules.symmetricAlgebra X F).mul i j).app W x y)) =
      (Ψ.right.hom.app W).hom ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl i x) *
        (Ψ.right.hom.app W).hom ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl j y)
    refine (congrArg (Ψ.right.hom.app W).hom
      (SheafOfModules.GradedAlgebra.ungradedIncl_mul _ i j x y).symm).trans ?_
    exact map_mul (Ψ.right.hom.app W).hom _ _
  map_one W := by
    change (Ψ.right.hom.app W).hom
        ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl 0
          ((Scheme.Modules.symmetricAlgebra X F).one.eval W)) = 1
    refine (congrArg (Ψ.right.hom.app W).hom
      (SheafOfModules.GradedAlgebra.ungradedIncl_one _ W)).trans ?_
    exact map_one (Ψ.right.hom.app W).hom

/-- **Every morphism of algebra sheaves out of `Sym(F)` is the lift of its degree-one part.**
This is the uniqueness half of the ungraded universal property of `Sym(F)`, which
`Stacks.SymAlgSheaf.algebraLift` does not claim: it is uniqueness in the graded universal
property of `Sym(F)` (`SheafOfModules.GradedAlgebra.IsUniversal.desc_unique`), applied to the
degreewise components of the morphism, transported across the sheafification that builds the
ungraded realization. -/
theorem eq_algebraLift
    (Ψ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜) :
    Ψ = algebraLift 𝒜 F (Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece 𝒜 F Ψ 1) := by
  have hgr : gradedHom 𝒜 F Ψ =
      descHom 𝒜 F (Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece 𝒜 F Ψ 1) :=
    SheafOfModules.GradedAlgebra.IsUniversal.desc_unique
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) (constGraded 𝒜) _
      (pairwiseCommutes_constGraded 𝒜 F _) rfl
  let α : (Scheme.Modules.symmetricAlgebra X F).ungradedSheaf ⟶
      Scheme.QuasicoherentAlgebra.ringSheaf 𝒜 := Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap Ψ
  have hα : α = ungradedLift 𝒜 F (Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece 𝒜 F Ψ 1) := by
    refine totalSheaf_hom_ext (Scheme.Modules.symmetricAlgebra X F) _ _ ?_
    refine Eq.trans ?_ (toTotalSheaf_comp_ungradedLift 𝒜 F _).symm
    refine NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext
      fun (z : (symPre F).Total W) => ?_))
    change (α.hom.app W).hom
        ((symPre F).totalUnit (Opens.grothendieckTopology (X : TopCat)) W z) =
      psiTotal 𝒜 F _ W z
    induction z using Stacks.GradedAlgebra.incl_induction with
    | zero =>
        refine (congrArg (α.hom.app W).hom
          (map_zero ((symPre F).totalUnit (Opens.grothendieckTopology (X : TopCat)) W))).trans ?_
        exact (map_zero (α.hom.app W).hom).trans (map_zero (psiTotal 𝒜 F _ W)).symm
    | incl n x =>
        have h1 : (α.hom.app W).hom
            ((symPre F).totalUnit (Opens.grothendieckTopology (X : TopCat)) W
              ((symPre F).incl n x)) = (homPiece 𝒜 F Ψ n).val.app W x :=
          rfl
        have h2 : (homPiece 𝒜 F Ψ n).val.app W x =
            ((descHom 𝒜 F (Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece 𝒜 F Ψ 1)).app
              n).val.app W x :=
          congrArg (fun g : SheafOfModules.GradedAlgebra.UnitalHom
            (Scheme.Modules.symmetricAlgebra X F) (constGraded 𝒜) => (g.app n).val.app W x) hgr
        exact h1.trans (h2.trans ((psiAdd_apply 𝒜 F _ n W x).symm.trans
          (psiTotal_incl 𝒜 F _ n W x).symm))
    | add a b ha hb =>
        refine (congrArg (α.hom.app W).hom
          (map_add ((symPre F).totalUnit (Opens.grothendieckTopology (X : TopCat)) W) a b)).trans ?_
        refine (map_add (α.hom.app W).hom _ _).trans ?_
        exact (congrArg₂ (· + ·) ha hb).trans (map_add (psiTotal 𝒜 F _ W) a b).symm
  exact Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun W =>
    CommRingCat.hom_ext (RingHom.ext fun z =>
      (congrArg (fun t : (Scheme.Modules.symmetricAlgebra X F).ungradedSheaf ⟶
          Scheme.QuasicoherentAlgebra.ringSheaf 𝒜 => (t.hom.app W).hom z) hα).trans
        (algebraLift_right_app 𝒜 F _ W z).symm))))

/-- The degree-one generator of `Sym(F)`, as a morphism into the module underlying the algebra
sheaf `Sym(F)`: a local section `s` of `F` is sent to the image of the degree-one section `s` in
the ungraded realization. -/
def symmetricAlgebraSheafι :
    F ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
      (Scheme.Modules.symmetricAlgebraSheaf X F) :=
  Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece _ F (𝟙 _) 1

/-- The degree-one generator followed by a morphism of algebra sheaves out of `Sym(F)` is the
degree-one component of the morphism on the generator. -/
theorem symmetricAlgebraSheafι_comp_underlyingModuleMap
    (Ψ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜) :
    symmetricAlgebraSheafι F ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap Ψ =
      Scheme.Modules.symmetricAlgebraGen X F ≫ homPiece 𝒜 F Ψ 1 :=
  rfl

/-- **The lift out of `Sym(F)` restricts to the given morphism on the generator.** -/
theorem symmetricAlgebraSheafι_comp_algebraLift
    (φ : F ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule 𝒜) :
    symmetricAlgebraSheafι F ≫
        Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap (algebraLift 𝒜 F φ) = φ := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  exact algebraLift_ungradedIncl_gen 𝒜 F φ W s

/-- **Morphisms of algebra sheaves out of `Sym(F)` are determined by their restriction to the
generator.** -/
theorem algebraHom_ext
    {Ψ₁ Ψ₂ : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜}
    (h : symmetricAlgebraSheafι F ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap Ψ₁ =
      symmetricAlgebraSheafι F ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap Ψ₂) :
    Ψ₁ = Ψ₂ := by
  rw [eq_algebraLift 𝒜 F Ψ₁, eq_algebraLift 𝒜 F Ψ₂]
  exact congrArg (algebraLift 𝒜 F) h

end Stacks.SymAlgSheaf

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec.AlgebraSheaf

variable {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules)

/-- The comparison `g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ Sym(g^*M)`: the transpose, under the adjunction
between pullback and direct image of algebra sheaves, of the lift out of `Sym(M)` of the unit
`M ⟶ g_* g^* M` followed by the generator of `Sym(g^* M)`. -/
def symmetricAlgebraPullbackHom :
    (algebraPullback g).obj (symmetricAlgebraSheaf S M) ⟶
      symmetricAlgebraSheaf T ((pullback g).obj M) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm
    (algebraLift ((algebraPushforward g).obj (symmetricAlgebraSheaf T ((pullback g).obj M))) M
      ((pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M))))

/-- The comparison `Sym(g^*M) ⟶ g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T`: the lift out of `Sym(g^* M)` of the
transpose of the generator of `Sym(M)` followed by the unit of the adjunction between pullback and
direct image of algebra sheaves. -/
def symmetricAlgebraPullbackInv :
    symmetricAlgebraSheaf T ((pullback g).obj M) ⟶
      (algebraPullback g).obj (symmetricAlgebraSheaf S M) :=
  algebraLift ((algebraPullback g).obj (symmetricAlgebraSheaf S M)) ((pullback g).obj M)
    (((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      (symmetricAlgebraSheafι M ≫ underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app (symmetricAlgebraSheaf S M))))

/-- The module morphism underlying the direct image of a morphism of algebra sheaves is the direct
image of the underlying module morphism. -/
theorem underlyingModuleMap_algebraPushforward_map {B B' : Stacks.RelativeSpec.AlgebraSheaf T}
    (f : B ⟶ B') :
    underlyingModuleMap ((algebraPushforward g).map f) =
      (pushforward g).map (underlyingModuleMap f) :=
  rfl

/-- The generator of `Sym(g^* M)` mapped into the pulled-back algebra by the comparison. -/
theorem symmetricAlgebraSheafι_comp_symmetricAlgebraPullbackInv :
    symmetricAlgebraSheafι ((pullback g).obj M) ≫
        underlyingModuleMap (symmetricAlgebraPullbackInv g M) =
      ((pullbackPushforwardAdjunction g).homEquiv M
          (underlyingModule ((algebraPullback g).obj (symmetricAlgebraSheaf S M)))).symm
        (symmetricAlgebraSheafι M ≫ underlyingModuleMap
          ((algebraPullbackPushforwardAdjunction g).unit.app (symmetricAlgebraSheaf S M))) :=
  symmetricAlgebraSheafι_comp_algebraLift _ _ _

/-- The transpose of the comparison `g⁺ Sym(M) ⟶ Sym(g^* M)` is the lift it is built from. -/
theorem homEquiv_symmetricAlgebraPullbackHom :
    (algebraPullbackPushforwardAdjunction g).homEquiv _ _ (symmetricAlgebraPullbackHom g M) =
      algebraLift ((algebraPushforward g).obj (symmetricAlgebraSheaf T ((pullback g).obj M))) M
        ((pullbackPushforwardAdjunction g).unit.app M ≫
          (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M))) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

/-- The underlying module morphism of a composite of algebra sheaf morphisms is the composite. -/
private theorem underlyingModuleMap_comp_eq {X : Scheme.{u}}
    {A B C : Stacks.RelativeSpec.AlgebraSheaf X}
    (f : A ⟶ B) (h : B ⟶ C) :
    underlyingModuleMap (f ≫ h) = underlyingModuleMap f ≫ underlyingModuleMap h :=
  (underlyingModuleFunctor X).map_comp f h

/-- The underlying module morphism of the identity of an algebra sheaf is the identity. -/
private theorem underlyingModuleMap_id_eq {X : Scheme.{u}}
    (A : Stacks.RelativeSpec.AlgebraSheaf X) :
    underlyingModuleMap (𝟙 A) = 𝟙 (underlyingModule A) :=
  (underlyingModuleFunctor X).map_id A

/-- The generator of `Sym(M)` followed by the module morphism underlying the transpose of the
comparison `g⁺ Sym(M) ⟶ Sym(g^* M)` is the unit followed by the direct image of the generator
of `Sym(g^* M)`. -/
private theorem symmetricAlgebraSheafι_comp_homEquiv_symmetricAlgebraPullbackHom :
    symmetricAlgebraSheafι M ≫ underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).homEquiv _ _ (symmetricAlgebraPullbackHom g M)) =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map (symmetricAlgebraSheafι ((pullback g).obj M)) :=
  (congrArg (fun t => symmetricAlgebraSheafι M ≫ underlyingModuleMap t)
    (homEquiv_symmetricAlgebraPullbackHom g M)).trans
    (symmetricAlgebraSheafι_comp_algebraLift _ _ _)

/-- The transpose of the generator of `Sym(M)` followed by the unit and the direct image of the
comparison `g⁺ Sym(M) ⟶ Sym(g^* M)` is the generator of `Sym(g^* M)`. -/
private theorem transpose_comp_pushforward_map_hom :
    ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((symmetricAlgebraSheafι M ≫ underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app (symmetricAlgebraSheaf S M))) ≫
      (pushforward g).map (underlyingModuleMap (symmetricAlgebraPullbackHom g M))) =
      symmetricAlgebraSheafι ((pullback g).obj M) := by
  refine (congrArg _ ((Category.assoc _ _ _).trans (congrArg (symmetricAlgebraSheafι M ≫ ·)
    ((underlyingModuleMap_comp_eq _ ((algebraPushforward g).map _)).symm.trans
      (congrArg underlyingModuleMap ((algebraPullbackPushforwardAdjunction g).homEquiv_unit _ _
        (symmetricAlgebraPullbackHom g M)).symm))))).trans ?_
  refine (congrArg _ ((symmetricAlgebraSheafι_comp_homEquiv_symmetricAlgebraPullbackHom g M).trans
    ((pullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm)).trans ?_
  exact Equiv.symm_apply_apply _ _

/-- The comparison `Sym(g^* M) ⟶ g⁺ Sym(M) ⟶ Sym(g^* M)` is the identity. -/
theorem symmetricAlgebraPullbackInv_hom :
    symmetricAlgebraPullbackInv g M ≫ symmetricAlgebraPullbackHom g M = 𝟙 _ := by
  refine algebraHom_ext _ _ ?_
  refine (congrArg (_ ≫ ·) (underlyingModuleMap_comp_eq _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (symmetricAlgebraSheafι_comp_symmetricAlgebraPullbackInv g M)).trans ?_
  refine ((pullbackPushforwardAdjunction g).homEquiv_naturality_right_symm _ _).symm.trans ?_
  refine (transpose_comp_pushforward_map_hom g M).trans ?_
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (underlyingModuleMap_id_eq _).symm)

/-- The comparison `g⁺ Sym(M) ⟶ Sym(g^* M) ⟶ g⁺ Sym(M)` is the identity. -/
theorem symmetricAlgebraPullbackHom_inv :
    symmetricAlgebraPullbackHom g M ≫ symmetricAlgebraPullbackInv g M = 𝟙 _ := by
  let adj := algebraPullbackPushforwardAdjunction g
  let madj := pullbackPushforwardAdjunction g
  let ι' := symmetricAlgebraSheafι ((pullback g).obj M)
  let hom := symmetricAlgebraPullbackHom g M
  let inv := symmetricAlgebraPullbackInv g M
  refine (adj.homEquiv _ _).injective ?_
  refine (adj.homEquiv_naturality_right hom inv).trans ?_
  refine Eq.trans ?_ (Eq.trans (adj.homEquiv_unit _ _ (𝟙 _))
    ((congrArg (adj.unit.app _ ≫ ·) ((algebraPushforward g).map_id _)).trans
      (Category.comp_id _))).symm
  refine algebraHom_ext _ _ ?_
  refine (congrArg (symmetricAlgebraSheafι M ≫ ·) (underlyingModuleMap_comp_eq _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ underlyingModuleMap ((algebraPushforward g).map inv))
    (symmetricAlgebraSheafι_comp_homEquiv_symmetricAlgebraPullbackHom g M)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (madj.unit.app M ≫ ·)
    ((pushforward g).map_comp ι' (underlyingModuleMap inv)).symm).trans ?_
  refine (congrArg (fun t => madj.unit.app M ≫ (pushforward g).map t)
    (symmetricAlgebraSheafι_comp_symmetricAlgebraPullbackInv g M)).trans ?_
  exact (madj.homEquiv_unit _ _ _).symm.trans ((madj.homEquiv _ _).apply_symm_apply _)

/-- **Stacks 01CI for the symmetric algebra sheaf**: the pullback
`g⁻¹ Sym(M) ⊗_{g⁻¹𝒪_S} 𝒪_T` of the algebra sheaf `Sym(M)` is `Sym(g^* M)`. -/
@[ega "II 1.7.5" "special case", ega "II 4.1.3" "(E)"]
def symmetricAlgebraSheafPullbackIso :
    (algebraPullback g).obj (symmetricAlgebraSheaf S M) ≅
      symmetricAlgebraSheaf T ((pullback g).obj M) where
  hom := symmetricAlgebraPullbackHom g M
  inv := symmetricAlgebraPullbackInv g M
  hom_inv_id := symmetricAlgebraPullbackHom_inv g M
  inv_hom_id := symmetricAlgebraPullbackInv_hom g M

private theorem symmetricAlgebraSheafι_comp_map_of_eq_algebraLift {X : Scheme.{u}}
    {F₁ F₂ : X.Modules} (φ : F₁ ⟶ F₂) :
    symmetricAlgebraSheafι F₁ ≫ underlyingModuleMap (symmetricAlgebraSheafMap X φ) =
      φ ≫ symmetricAlgebraSheafι F₂ := by
  have h1 : algebraLift (symmetricAlgebraSheaf X F₂) F₂ (symmetricAlgebraSheafι F₂) = 𝟙 _ :=
    (eq_algebraLift _ F₂ (𝟙 _)).symm
  have h2 : symmetricAlgebraSheafMap X φ =
      algebraLift (symmetricAlgebraSheaf X F₂) F₁ (φ ≫ symmetricAlgebraSheafι F₂) :=
    ((Category.comp_id _).symm.trans (congrArg (fun t => _ ≫ t) h1.symm)).trans
      (algebraLift_comp _ φ _).symm
  rw [h2]
  exact symmetricAlgebraSheafι_comp_algebraLift _ _ _

variable [_root_.SheafOfModules.IsQuasicoherent M]

/-- `Sym(M)` is a quasi-coherent algebra sheaf. The general instance
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf` is stated for a module
typed as `SheafOfModules S.ringCatSheaf`, which instance search does not identify with
`S.Modules`. -/
instance isQuasicoherent_symmetricAlgebraSheaf_modules :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (symmetricAlgebraSheaf S M) :=
  isQuasicoherent_symmetricAlgebraSheaf S M

/-- `Sym(g^* M)` is a quasi-coherent algebra sheaf. -/
instance isQuasicoherent_symmetricAlgebraSheaf_pullback :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (symmetricAlgebraSheaf T ((pullback g).obj M)) :=
  isQuasicoherent_symmetricAlgebraSheaf T _

omit [_root_.SheafOfModules.IsQuasicoherent M] in
/-- **Stacks 01CI for the symmetric algebra sheaf is natural in the module**: for
`f : M₁ ⟶ M₂`, the identifications `g⁻¹ Sym(Mᵢ) ⊗ 𝒪_T ≅ Sym(g^* Mᵢ)` intertwine the pullback of
`Sym(f)` with `Sym(g^* f)`. Both composites are determined, through the adjunction between
pullback and direct image of algebra sheaves and the universal property of `Sym(M₁)`, by the
module map `M₁ ⟶ g_* Sym(g^* M₂)`, which is `f` followed by the unit and the generator on
either side. -/
theorem symmetricAlgebraSheafPullbackIso_hom_naturality {M₁ M₂ : S.Modules} (f : M₁ ⟶ M₂) :
    (algebraPullback g).map (symmetricAlgebraSheafMap S f) ≫
        (symmetricAlgebraSheafPullbackIso g M₂).hom =
      (symmetricAlgebraSheafPullbackIso g M₁).hom ≫
        symmetricAlgebraSheafMap T ((pullback g).map f) := by
  let adj := algebraPullbackPushforwardAdjunction g
  let madj := pullbackPushforwardAdjunction g
  refine (adj.homEquiv _ _).injective ?_
  refine (adj.homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ (adj.homEquiv_naturality_right _ _).symm
  refine algebraHom_ext _ _ ?_
  refine (congrArg (symmetricAlgebraSheafι M₁ ≫ ·) (underlyingModuleMap_comp_eq _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (symmetricAlgebraSheafι_comp_map_of_eq_algebraLift f)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (f ≫ ·)
    (symmetricAlgebraSheafι_comp_homEquiv_symmetricAlgebraPullbackHom g M₂)).trans ?_
  refine Eq.trans ?_
    (congrArg (symmetricAlgebraSheafι M₁ ≫ ·) (underlyingModuleMap_comp_eq _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _)
    (symmetricAlgebraSheafι_comp_homEquiv_symmetricAlgebraPullbackHom g M₁)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (madj.unit.app M₁ ≫ ·) ((pushforward g).map_comp _
    (underlyingModuleMap (symmetricAlgebraSheafMap T ((pullback g).map f)))))
  refine Eq.trans ?_ (congrArg (fun t => madj.unit.app M₁ ≫ (pushforward g).map t)
    (symmetricAlgebraSheafι_comp_map_of_eq_algebraLift ((pullback g).map f))).symm
  refine Eq.trans ?_ (congrArg (madj.unit.app M₁ ≫ ·) ((pushforward g).map_comp
    ((pullback g).map f) (symmetricAlgebraSheafι ((pullback g).obj M₂)))).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (madj.unit.naturality f)

/-- **The pushed-forward structure sheaf of `𝐕(M) ×_S T ⟶ T` is `Sym(g^* M)`**: the
base-change comparison of Stacks 01LX (2) for the algebra `Sym(M)`, followed by Stacks 01CI. -/
def vectorBundlePullbackAlgebraIso :
    pushforwardAlgebra ((Over.pullback g).obj (vectorBundleOver S (F := M))).hom ≅
      symmetricAlgebraSheaf T ((pullback g).obj M) :=
  pullbackAlgebraIso g (symmetricAlgebraSheaf S M) ≪≫ symmetricAlgebraSheafPullbackIso g M

/-- **The vector bundle of a quasi-coherent module commutes with base change, as schemes over
the new base**: for `g : T ⟶ S` the fibre product `𝐕(M) ×_S T` is the vector bundle
`𝐕(g^* M)` over `T`. This is Stacks 01LX (2) for `Sym(M)`, followed by Stacks 01CI; the
isomorphism is exhibited from the identification of algebras
`AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso`, so that the algebra map it
induces is known (`pushforwardAlgebraMap_vectorBundlePullbackOverIso_hom`). -/
@[sga "3 VIIA 4.1.4" "more general", sga "6 0 2.9" "Clause"]
def vectorBundlePullbackOverIso :
    (Over.pullback g).obj (vectorBundleOver S (F := M)) ≅
      vectorBundleOver T (F := (pullback g).obj M) :=
  haveI := isAffineHom_vectorBundleOver S (F := M)
  haveI : IsAffineHom (Limits.pullback.snd (vectorBundleOver S (F := M)).hom g) :=
    isAffineHom_overPullback_hom g _
  relativeSpecOverIsoOfAlgebraIso _ (symmetricAlgebraSheaf T ((pullback g).obj M))
    (vectorBundlePullbackAlgebraIso g M)

/-- The algebra map induced by `𝐕(M) ×_S T ≅ 𝐕(g^* M)` is the inverse of
`vectorBundlePullbackAlgebraIso`, read through the identification
`(𝐕(g^* M) ⟶ T)_* 𝒪 ≅ Sym(g^* M)`. -/
theorem pushforwardAlgebraMap_vectorBundlePullbackOverIso_hom :
    pushforwardAlgebraMap (vectorBundlePullbackOverIso g M).hom =
      (vectorBundlePushforwardIso T (F := (pullback g).obj M)).hom ≫
        (vectorBundlePullbackAlgebraIso g M).inv :=
  have := isAffineHom_vectorBundleOver S (F := M)
  have : IsAffineHom (Limits.pullback.snd (vectorBundleOver S (F := M)).hom g) :=
    isAffineHom_overPullback_hom g _
  pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso
    ((Over.pullback g).obj (vectorBundleOver S (F := M))).hom
    (symmetricAlgebraSheaf T ((pullback g).obj M)) (vectorBundlePullbackAlgebraIso g M)

/-- **The identification `𝐕(M) ×_S T ≅ 𝐕(g^* M)` is natural in the module**: for a morphism
`f : M₁ ⟶ M₂` of quasi-coherent modules it intertwines the base change of `𝐕(f)` with
`𝐕(g^* f)`. Both are morphisms over `T` into a scheme affine over `T`, so it suffices to compare
the algebra maps they induce, which is the naturality of the base-change comparison of
Stacks 01LX (2) and of `symmetricAlgebraSheafPullbackIso`. -/
@[ega "II 1.7.11" "(iv)"]
theorem vectorBundlePullbackOverIso_hom_naturality {M₁ M₂ : S.Modules}
    [_root_.SheafOfModules.IsQuasicoherent M₁] [_root_.SheafOfModules.IsQuasicoherent M₂]
    (f : M₁ ⟶ M₂) :
    (Over.pullback g).map (vectorBundleMap S f) ≫ (vectorBundlePullbackOverIso g M₁).hom =
      (vectorBundlePullbackOverIso g M₂).hom ≫ vectorBundleMap T ((pullback g).map f) := by
  have := isAffineHom_vectorBundleOver T (F := (pullback g).obj M₁)
  have := Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent g
    (symmetricAlgebraSheaf S M₁) inferInstance
  have hsym : (symmetricAlgebraSheafPullbackIso g M₁).inv ≫
        (algebraPullback g).map (symmetricAlgebraSheafMap S f) =
      symmetricAlgebraSheafMap T ((pullback g).map f) ≫
        (symmetricAlgebraSheafPullbackIso g M₂).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← symmetricAlgebraSheafPullbackIso_hom_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinv : ∀ (N : S.Modules) [_root_.SheafOfModules.IsQuasicoherent N],
      (vectorBundlePullbackAlgebraIso g N).inv =
        (symmetricAlgebraSheafPullbackIso g N).inv ≫
          (algebraPullback g).map (vectorBundlePushforwardIso S (F := N)).inv ≫
            baseChangeAlgebraHom g (vectorBundleOver S (F := N)) := fun _ _ => rfl
  have key : (vectorBundlePullbackAlgebraIso g M₁).inv ≫
        pushforwardAlgebraMap ((Over.pullback g).map (vectorBundleMap S f)) =
      symmetricAlgebraSheafMap T ((pullback g).map f) ≫
        (vectorBundlePullbackAlgebraIso g M₂).inv := by
    rw [hinv, hinv, Category.assoc, Category.assoc,
      ← baseChangeAlgebraHom_naturality g (vectorBundleMap S f),
      pushforwardAlgebraMap_vectorBundleMap S f, ← Category.assoc
      ((algebraPullback g).map (vectorBundlePushforwardIso S (F := M₁)).inv),
      ← Functor.map_comp, Iso.inv_hom_id_assoc, Functor.map_comp]
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ _) hsym).trans (Category.assoc _ _ _)
  refine eq_of_pushforwardAlgebraMap_eq ?_
  refine (pushforwardAlgebraMap_comp _ _).trans ?_
  refine Eq.trans ?_ (pushforwardAlgebraMap_comp _ _).symm
  refine (congrArg (· ≫ _) (pushforwardAlgebraMap_vectorBundlePullbackOverIso_hom g M₁)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·)
    (pushforwardAlgebraMap_vectorBundleMap T ((pullback g).map f)).symm
    (pushforwardAlgebraMap_vectorBundlePullbackOverIso_hom g M₂).symm)
  rw [Category.assoc, key]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The vector bundle of a quasi-coherent module commutes with base change**: for
`g : T ⟶ S` the fibre product `𝐕(M) ×_S T` is the vector bundle `𝐕(g^* M)` over `T`. This is
`vectorBundlePullbackOverIso` on underlying schemes. -/
def vectorBundlePullbackIso :
    Limits.pullback (vectorBundleToBase S M) g ≅ vectorBundle T ((pullback g).obj M) :=
  (Over.forget T).mapIso (vectorBundlePullbackOverIso g M)

/-- The identification `𝐕(M) ×_S T ≅ 𝐕(g^* M)` is an isomorphism over `T`. -/
@[reassoc (attr := simp)]
theorem vectorBundlePullbackIso_hom_vectorBundleToBase :
    (vectorBundlePullbackIso g M).hom ≫ vectorBundleToBase T ((pullback g).obj M) =
      Limits.pullback.snd (vectorBundleToBase S M) g :=
  Over.w (vectorBundlePullbackOverIso g M).hom

end AlgebraicGeometry.Scheme.Modules
