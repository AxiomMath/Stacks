module

public import Mathlib.RingTheory.Flat.Stability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Descent of the resolution property along a finite locally free morphism

[Stacks, Tag 0GTC]: a surjective finite locally free morphism of schemes carries the resolution
property from its source to its target.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_surjective_isFiniteLocallyFree`: the resolution
  property of the target of a surjective finite locally free morphism.

## Implementation notes

Let `f : X ⟶ Y` be surjective and finite locally free and let `𝒢` be a finite type
quasi-coherent `𝒪_Y`-module. The resolution property of `X`, applied to the finite type
quasi-coherent module `f^*𝒢`, gives a finite locally free `ℰ` on `X` and an epimorphism
`p : ℰ ⟶ f^*𝒢`. Write `ℬ = f_*𝒪_X` and `𝒜 = f_*ℰ`.

* `𝒜` is finite locally free. A finite locally free module is flat and of finite presentation;
  flatness over a base passes to the direct image along an affine morphism
  ([Stacks, Tag 0FLM]) and, over the base `Y` itself, flatness over a base is flatness; finite
  presentation passes to the direct image along a finite morphism of finite presentation
  ([Stacks, Tag 05B4]).
* `ℬ` is finite locally free by the definition of a finite locally free morphism, so its dual
  `ℬ^∨` is finite locally free too and the two carry an exact pairing
  ([Stacks, Tag 0FA7], [Stacks, Tag 0FNV]).
* The projection formula for the affine morphism `f` ([Stacks, Tag 0FZE]), taken at the
  structure sheaf, gives `ℬ ⊗ 𝒢 ≅ f_*(𝒪_X ⊗ f^*𝒢) ≅ f_*f^*𝒢`. Direct image along an affine
  morphism is exact on quasi-coherent modules, so `f_*p` followed by the inverse of that
  isomorphism is an epimorphism `r : 𝒜 ⟶ ℬ ⊗ 𝒢`.
* The adjunction `ℬ^∨ ⊗ - ⊣ ℬ ⊗ -` coming from the exact pairing transposes `r` into
  `q : ℬ^∨ ⊗ 𝒜 ⟶ 𝒢`, and `ℬ^∨ ⊗ 𝒜` is finite locally free, being a tensor product of two
  finite locally free modules.

Only the surjectivity of `q` needs an argument. Its image `ℬ ⊗ q` under the right adjoint is an
epimorphism, because `r` factors through it, and `ℬ ⊗ -` is injective on morphisms of
quasi-coherent modules: the projection formula identifies it with `f_*f^*(-)`, direct image
along an affine morphism is faithful on quasi-coherent modules, and pullback along a flat
surjective morphism is injective on morphisms. Quasi-coherent modules are closed under
cokernels, so a functor injective on morphisms between them reflects epimorphisms: the
cokernel projection of `q` is killed, hence zero.

Injectivity of the pullback on morphisms is proved from stalks rather than from flat descent.
A morphism of sheaves of modules vanishes exactly when all of its stalks do, pullback is
additive, and the stalk of a pullback along a flat morphism at `x` vanishes exactly when the
stalk of the original at `f x` does; surjectivity of `f` then covers every point of `Y`.

## References

* [Stacks Project, Tag 0GTC](https://stacks.math.columbia.edu/tag/0GTC)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.AlgebraicGeometry.ModuleLimits (affinePushforwardFaithful)

universe v u

namespace AlgebraicGeometry

/-! ### Tensoring with the unit -/

/-- Tensoring on the left with the monoidal unit is injective on morphisms. -/
private theorem eq_of_tensorHom_id_eq {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (U : C) (hU : U = 𝟙_ C) {M N : C} {a b : M ⟶ N}
    (h : 𝟙 U ⊗ₘ a = 𝟙 U ⊗ₘ b) : a = b := by
  subst hU
  rw [id_tensorHom, id_tensorHom] at h
  exact (cancel_epi (λ_ M).hom).1 (by rw [← leftUnitor_naturality, ← leftUnitor_naturality, h])

/-- Tensoring on the left with the structure sheaf is injective on morphisms of sheaves of
modules on a ringed space. -/
private theorem tensorSheafMap_unit_injective {X : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing X)} {a b : M ⟶ N}
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 (SheafOfModules.unit (structureSheafRing X))), a) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((𝟙 (SheafOfModules.unit (structureSheafRing X))), b) : (_, _) ⟶ (_, _)))) :
    a = b := by
  let m := Stacks.SheafOfModules.OnSpace.monoidal X
  have hc := (Stacks.SheafOfModules.OnSpace.monoidal_tensorHom X
      (𝟙 (SheafOfModules.unit (structureSheafRing X))) a).trans
    (h.trans (Stacks.SheafOfModules.OnSpace.monoidal_tensorHom X
      (𝟙 (SheafOfModules.unit (structureSheafRing X))) b).symm)
  refine eq_of_tensorHom_id_eq _
    (Stacks.SheafOfModules.OnSpace.monoidal_tensorUnit X).symm ?_
  exact (Iso.cancel_iso_hom_right _ _
      (eqToIso (Stacks.SheafOfModules.OnSpace.monoidal_tensorObj X
        (SheafOfModules.unit (structureSheafRing X)) N))).1
    ((Iso.cancel_iso_hom_left
      (eqToIso (Stacks.SheafOfModules.OnSpace.monoidal_tensorObj X
        (SheafOfModules.unit (structureSheafRing X)) M).symm) _ _).1 hc)

/-! ### Faithfulness of pullback along a surjective flat morphism -/

/-- Pullback along a surjective flat morphism of schemes is injective on morphisms: a morphism
whose pullback vanishes has vanishing stalks at every point of the target. -/
private theorem pullback_map_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    {M N : Y.Modules} {a b : M ⟶ N}
    (h : (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map b) : a = b := by
  have h0 : (Scheme.Modules.pullback f).map (a - b) = 0 := by
    rw [CategoryTheory.Functor.map_sub, h, sub_self]
  have hz := (SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero X.ringCatSheaf
    ((Scheme.Modules.pullback f).map (a - b))).1 h0
  rw [← sub_eq_zero]
  refine (SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero Y.ringCatSheaf (a - b)).2 fun y m => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  exact (stalkMap_modulePullback_eq_zero_iff f (a - b) x).1 (hz x) m

/-! ### The direct image of a finite locally free module -/

/-- A flat module on the source of a flat morphism of schemes is flat over the target. -/
private theorem isFlatOver_of_isFlat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (E : X.Modules)
    (hE : SheafOfModules.IsFlat (C := Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E) :
    IsFlatOver f.toLRSHom.toShHom E := by
  intro x
  let alg : Algebra (Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (X.presheaf.stalk x) :=
    (f.toLRSHom.toShHom.hom.stalkMap x).hom.toAlgebra
  let mod : Module (Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf x) :=
    Module.compHom _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
  let tower : IsScalarTower (Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h1 : Module.Flat (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf x) :=
    (SheafOfModules.isFlat_iff_stalk_flat X.sheaf E).mp hE x
  have h2 : Module.Flat (Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (X.presheaf.stalk x) := Flat.stalkMap f x
  exact @Module.Flat.trans _ (X.presheaf.stalk x) _ _ _ alg _ mod inferInstance tower h2 h1

/-- A finite locally free module on a scheme is quasi-coherent, being of finite presentation. -/
private theorem isQuasicoherent_of_isFiniteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M] :
    M.IsQuasicoherent := by
  obtain ⟨σ, -⟩ := (Stacks.FiniteLocallyFree.isFinitePresentation M).1
  exact σ.isQuasicoherent

/-- The direct image of a finite locally free module along a finite locally free morphism is
finite locally free. -/
private theorem isFiniteLocallyFree_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj E) := by
  have hfin := Stacks.Morphisms.IsFiniteLocallyFree.isFinite f
  have hfp := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation f
  have hflat := Stacks.Morphisms.IsFiniteLocallyFree.flat f
  have hqcE : E.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree E
  have hE := ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae E).out 4 1).mp
    (inferInstance : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
  have hqc := Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom f E hqcE
  have hflat' := (isFlatOver_id_iff_isFlat ((Scheme.Modules.pushforward f).obj E)).mp
    ((isFlatOver_pushforward_iff f (𝟙 Y) E).mp
      (by simpa only [Category.comp_id] using isFlatOver_of_isFlat f E hE.1))
  have hfp' := (isFinitePresentation_iff_pushforward_isFinitePresentation f
    ⟨hfp, inferInstance, inferInstance⟩ E).mp hE.2
  exact ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae
    ((Scheme.Modules.pushforward f).obj E)).out 1 4).mp (And.intro hflat' hfp')

/-- The tensor product of two finite locally free modules on a scheme is finite locally free. -/
private theorem isFiniteLocallyFree_tensorSheaf {X : Scheme.{u}} (E F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) := by
  exact isFiniteLocallyFree_tensorObj E F

/-! ### Transposing an epimorphism along an adjunction -/

/-- A morphism is an epimorphism as soon as its image under a functor injective on morphisms
between objects with a cokernel-stable property is one. -/
private theorem epi_of_epi_map_of_injective {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderCokernels] (R : C ⥤ C)
    (hinj : ∀ {M N : C}, P M → P N → ∀ {a b : M ⟶ N}, R.map a = R.map b → a = b)
    {A B : C} (q : A ⟶ B) (hA : P A) (hB : P B) [Epi (R.map q)] : Epi q := by
  have hπ : cokernel.π q = 0 := by
    apply hinj hB (P.prop_cokernel q hA hB)
    apply (cancel_epi (R.map q)).1
    simp only [← R.map_comp, cokernel.condition, comp_zero]
  apply (Preadditive.epi_iff_isZero_cokernel q).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (cokernel.π q)).1
  simp [hπ]

/-- The adjoint transpose of an epimorphism into a value of the right adjoint is an
epimorphism, when the right adjoint is injective on morphisms between objects with the given
cokernel-stable property. -/
private theorem epi_adjunction_homEquiv_symm {C : Type u} [Category.{v} C] [Abelian C]
    {L R : C ⥤ C} (adj : L ⊣ R) (P : ObjectProperty C) [P.IsClosedUnderCokernels]
    (hinj : ∀ {M N : C}, P M → P N → ∀ {a b : M ⟶ N}, R.map a = R.map b → a = b)
    {A B : C} (p : A ⟶ R.obj B) [hp : Epi p] (hA : P (L.obj A)) (hB : P B) :
    Epi ((adj.homEquiv A B).symm p) := by
  have he : adj.unit.app A ≫ R.map ((adj.homEquiv A B).symm p) = p :=
    (adj.homEquiv_unit A B _).symm.trans ((adj.homEquiv A B).apply_symm_apply p)
  have : Epi (R.map ((adj.homEquiv A B).symm p)) := epi_of_epi_fac he
  exact epi_of_epi_map_of_injective P R hinj _ hA hB

/-! ### The descent -/

/-- Tensoring with the direct image of the structure sheaf of a surjective affine flat morphism
is injective on morphisms of quasi-coherent modules. -/
private theorem tensorSheafMap_pushforwardStructureSheaf_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] {M N : Y.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {a b : M ⟶ N}
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩)).map
          (((𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f)), a) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩)).map
          (((𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f)), b) : (_, _) ⟶ (_, _)))) :
    a = b := by
  have iM := isIso_projectionFormulaMap f (SheafOfModules.unit X.ringCatSheaf) M
    inferInstance inferInstance
  have iN := isIso_projectionFormulaMap f (SheafOfModules.unit X.ringCatSheaf) N
    inferInstance inferInstance
  have ha := projectionFormulaIso_hom_natural f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) a
  have hb := projectionFormulaIso_hom_natural f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) b
  have ht' := (Iso.cancel_iso_hom_left
    (projectionFormulaIso f (SheafOfModules.unit X.ringCatSheaf) M) _ _).1
    (ha.symm.trans ((congrArg (· ≫ (projectionFormulaIso f
      (SheafOfModules.unit X.ringCatSheaf) N).hom) h).trans hb))
  have hqcU : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := inferInstance
  have hqcM : ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := inferInstance
  have hqcN : ((Scheme.Modules.pullback f).obj N).IsQuasicoherent := inferInstance
  exact pullback_map_injective f (tensorSheafMap_unit_injective
    (affinePushforwardFaithful.{u} f
      (@tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hqcU hqcM)
      (@tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hqcU hqcN) _ _ ht'))

/-- **Stacks Project, Tag 0GTC.** If `f : X ⟶ Y` is a surjective finite locally free morphism of
schemes and `X` has the resolution property, then so does `Y`. -/
@[stacks 0GTC]
theorem hasResolutionProperty_of_surjective_isFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [Stacks.Morphisms.IsFiniteLocallyFree f] [HasResolutionProperty X] :
    HasResolutionProperty Y := by
  have hflat := Stacks.Morphisms.IsFiniteLocallyFree.flat f
  rw [hasResolutionProperty_iff]
  intro G hGqc hGft
  obtain ⟨E, hE, p, hp⟩ := HasResolutionProperty.exists_finiteLocallyFree_quotient
    ((Scheme.Modules.pullback f).obj G)
  have hqcE : E.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree E
  have hA : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj E) := isFiniteLocallyFree_pushforward f E
  have hB : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
      (Stacks.Morphisms.pushforwardStructureSheaf f) := inferInstance
  obtain ⟨m, _hunit, htensor, htensorMap, pairing, _, _⟩ :=
    Stacks.SheafOfModules.OnSpace.dualSheaf_isLeftDual Y.toRingedSpace
      (Stacks.Morphisms.pushforwardStructureSheaf f)
      (@Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
        Y.toRingedSpace (Stacks.Morphisms.pushforwardStructureSheaf f) hB)
  let mono : MonoidalCategory Y.Modules := m
  let pair : ExactPairing (Stacks.Morphisms.pushforwardStructureSheaf f)
      (Stacks.SheafOfModules.OnSpace.dualSheaf Y.toRingedSpace
        (Stacks.Morphisms.pushforwardStructureSheaf f)) := pairing
  have hD : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
      (Stacks.SheafOfModules.OnSpace.dualSheaf Y.toRingedSpace
        (Stacks.Morphisms.pushforwardStructureSheaf f)) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf
      (Stacks.Morphisms.pushforwardStructureSheaf f) inferInstance
  have hpf := isIso_projectionFormulaMap f (SheafOfModules.unit X.ringCatSheaf) G
    inferInstance inferInstance
  let e : Stacks.Morphisms.pushforwardStructureSheaf f ⊗ G ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G) :=
    eqToIso (htensor _ G) ≪≫ projectionFormulaIso f (SheafOfModules.unit X.ringCatSheaf) G ≪≫
      (Scheme.Modules.pushforward f).mapIso
        (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace
          ((Scheme.Modules.pullback f).obj G))
  have hqcD := isQuasicoherent_of_isFiniteLocallyFree
    (Stacks.SheafOfModules.OnSpace.dualSheaf Y.toRingedSpace
      (Stacks.Morphisms.pushforwardStructureSheaf f))
  have hqcA := isQuasicoherent_of_isFiniteLocallyFree ((Scheme.Modules.pushforward f).obj E)
  have hpe : Epi ((Scheme.Modules.pushforward f).map p) :=
    Stacks.AlgebraicGeometry.AffineQcohExactness.epi_pushforward_map f p
  have hepi : Epi ((Scheme.Modules.pushforward f).map p ≫ e.inv) := epi_comp _ _
  refine ⟨Stacks.SheafOfModules.OnSpace.dualSheaf Y.toRingedSpace
      (Stacks.Morphisms.pushforwardStructureSheaf f) ⊗ (Scheme.Modules.pushforward f).obj E,
    ?_, (tensorLeftAdjunction (Stacks.Morphisms.pushforwardStructureSheaf f)
      (Stacks.SheafOfModules.OnSpace.dualSheaf Y.toRingedSpace
        (Stacks.Morphisms.pushforwardStructureSheaf f))).homEquiv _ G |>.symm
      ((Scheme.Modules.pushforward f).map p ≫ e.inv), ?_⟩
  · exact SheafOfModules.IsFiniteLocallyFree.of_iso (eqToIso (htensor _ _)).symm
      (h := isFiniteLocallyFree_tensorSheaf _ _)
  · refine epi_adjunction_homEquiv_symm _ (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ?_ _ (hp := hepi) ?_ hGqc
    · intro M N hM hN a b hab
      have hab' : (𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f) ⊗ₘ a) =
          (𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f) ⊗ₘ b) :=
        (id_tensorHom (Stacks.Morphisms.pushforwardStructureSheaf f) a).trans
          (hab.trans (id_tensorHom (Stacks.Morphisms.pushforwardStructureSheaf f) b).symm)
      refine tensorSheafMap_pushforwardStructureSheaf_injective f ?_
      exact (htensorMap (𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f)) a).symm.trans
        ((congrArg (fun k =>
            eqToHom (htensor (Stacks.Morphisms.pushforwardStructureSheaf f) M).symm ≫ k ≫
              eqToHom (htensor (Stacks.Morphisms.pushforwardStructureSheaf f) N)) hab').trans
          (htensorMap (𝟙 (Stacks.Morphisms.pushforwardStructureSheaf f)) b))
    · exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
        (eqToIso (htensor _ _)).symm
        (@tensorSheaf_isQuasicoherent Y.toRingedSpace _ _ hqcD hqcA)

end AlgebraicGeometry

end
