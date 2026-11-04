module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of a tensor product of sheaves of modules

On a ringed space, restriction to an open commutes with the tensor product of sheaves of modules.
Consequently the tensor product of a coherent sheaf of modules with a locally trivial one is
coherent, the tensor product of a sheaf of modules of finite presentation with a coherent one is
coherent, and the tensor product of two coherent sheaves of modules is coherent.

## Main definitions

* `Stacks.SheafOfModules.TensorOver.tensorOverHom`: the canonical morphism from the tensor
  product, formed on the slice site at `U`, of the restrictions of `M` and `N` to the
  restriction of `M ⊗ N`.
* `Stacks.SheafOfModules.TensorOver.tensorLeftOver`: tensoring on the left by `G|_U` on the
  slice site at `U`.

## Main results

* `Stacks.SheafOfModules.TensorOver.tensorOverIso`: `(M ⊗ N)|_U ≅ M|_U ⊗ N|_U`, the right-hand
  tensor product being formed on the slice site at `U`.
* `Stacks.SheafOfModules.TensorOver.tensorOverIsoOfTrivial`: if `N|_U` is the structure sheaf,
  then `(M ⊗ N)|_U ≅ M|_U`.
* `Stacks.SheafOfModules.TensorOver.isCoherent_tensorSheaf_of_isLocallyTrivial`: the tensor
  product of a coherent sheaf of modules with a locally trivial one is coherent.
* `Stacks.SheafOfModules.TensorOver.isFiniteType_pullback_of_generatingSections`: the pullback of
  a short exact sequence with finite type sub-object along a morphism out of a sheaf with finitely
  many generating sections is of finite type.
* `Stacks.SheafOfModules.TensorOver.isCoherentOn_of_cokernel`: a sheaf of modules that is, on
  every open below `W`, the cokernel of a morphism from a sheaf of finite type into the
  restriction of a coherent sheaf is coherent on `W`.
* `Stacks.SheafOfModules.TensorOver.isCoherentOn_tensorSheaf_of_presentation`: if `F|_U` has a
  finite presentation and `G` is coherent, then `G ⊗ F` is coherent on `U`.
* `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent_of_isFinitePresentation`: the tensor
  product of a sheaf of modules of finite presentation with a coherent one is coherent.
* `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`: the tensor product of two coherent
  sheaves of modules is coherent.
* `AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible`: on a scheme, the
  tensor product of a coherent sheaf of modules with an invertible one is coherent.
* `AlgebraicGeometry.twistedSheaf_isCoherent`: every twist of a coherent sheaf of modules by
  invertible sheaves of modules is coherent.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (JX O)

universe u

namespace Stacks.SheafOfModules.TensorOver

variable {X : AlgebraicGeometry.RingedSpace.{u, u}} (U : Opens X.carrier)

/-! ### The slice site at an open, and the structure sheaf on it -/

/-- The structure presheaf of commutative rings restricted to the slice site at `U`. -/
noncomputable abbrev OU : (Over U)ᵒᵖ ⥤ CommRingCat.{u} := (X.sheaf.over U).obj

/-- The restricted structure presheaf is a sheaf of rings on the slice site. -/
theorem hOU : Presheaf.IsSheaf ((JX X).over U)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (OU (X := X) U)) :=
  (Presheaf.isSheaf_iff_isSheaf_comp _ (X.sheaf.over U).obj (forget₂ CommRingCat RingCat)).mp
    (X.sheaf.over U).property

/-- The restricted structure sheaf of rings on the slice site at `U`. -/
noncomputable abbrev RU : Sheaf ((JX X).over U) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (OU (X := X) U) (hOU U)

/-- The restricted structure sheaf `RU U` is `(structureSheafRing X).over U`. -/
theorem RU_eq : RU (X := X) U = (structureSheafRing X).over U := rfl

/-- The restriction of a sheaf of modules to the slice site at `U`, as a sheaf of modules
over `RU U`. -/
noncomputable def ov (M : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (RU (X := X) U) := M.over U

/-- The restriction `ov U M` is `M.over U`. -/
theorem ov_eq (M : SheafOfModules.{u} (structureSheafRing X)) : ov U M = M.over U := rfl

/-- The restriction of presheaves of modules to the slice site at `U`. -/
noncomputable abbrev resP :
    PresheafOfModules.{u} (O X) ⥤ PresheafOfModules.{u} (RU (X := X) U).obj :=
  PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)

/-- Restricting the underlying presheaf of `M` gives the underlying presheaf of `ov U M`. -/
theorem resP_obj_val (M : SheafOfModules.{u} (structureSheafRing X)) :
    (resP (X := X) U).obj M.val = (ov U M).val := rfl

/-! ### Restriction of the sheafification unit -/

/-- The restriction to the slice site at `U` of the unit of the sheafification adjunction. -/
noncomputable def gammaU (P : PresheafOfModules.{u} (O X)) :
    (resP (X := X) U).obj P ⟶ (ov U ((TensorStalkRingedSpace.sheafifyFunctor X).obj P)).val :=
  (resP (X := X) U).map (TensorStalkRingedSpace.sheafifyUnit X P)

/-- The restricted sheafification unit is locally bijective. -/
theorem w_gammaU (P : PresheafOfModules.{u} (O X)) :
    ((JX X).over U).W
      ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map (gammaU (X := X) U P)) := by
  have h : (JX X).W
      ((PresheafOfModules.toPresheaf (O X)).map (TensorStalkRingedSpace.sheafifyUnit X P)) :=
    (JX X).W_toSheafify P.presheaf
  have := h.isLocallyInjective
  have := h.isLocallySurjective
  exact (((JX X).over U).W_iff_isLocallyBijective _).2
    ⟨Presheaf.isLocallyInjective_whisker ((JX X).over U) (JX X) (Over.forget U)
      ((PresheafOfModules.toPresheaf (O X)).map (TensorStalkRingedSpace.sheafifyUnit X P)),
      Presheaf.isLocallySurjective_whisker ((JX X).over U) (JX X) (Over.forget U)
      ((PresheafOfModules.toPresheaf (O X)).map (TensorStalkRingedSpace.sheafifyUnit X P))⟩

/-! ### The comparison morphism -/

/-- The restriction to the slice site of the presheaf tensor product is the presheaf tensor
product of the restrictions: both have `M(V) ⊗_{O(V)} N(V)` as sections over `V ≤ U`. -/
noncomputable def resTensorIso (M N : SheafOfModules.{u} (structureSheafRing X)) :
    (resP (X := X) U).obj ((PresheafOfModules.tensorObj (O := (X).presheaf) (M.val) (N.val))) ≅
      (PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U
        N).val)) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The canonical locally bijective morphism from the slice-site tensor presheaf of the
restrictions into the restriction of the tensor sheaf. -/
noncomputable def deltaU (M N : SheafOfModules.{u} (structureSheafRing X)) :
    (PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U
      N).val)) ⟶
      (ov U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
          (N)))).val :=
  (resTensorIso U M N).inv ≫ gammaU U ((PresheafOfModules.tensorObj (O := (X).presheaf) (M.val)
      (N.val)))

/-- The underlying morphism of presheaves of abelian groups of `deltaU U M N` is the composite
of those of `(resTensorIso U M N).inv` and of the restricted sheafification unit. -/
theorem toPresheaf_map_deltaU (M N : SheafOfModules.{u} (structureSheafRing X)) :
    (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map (deltaU (X := X) U M N)
      = (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map (resTensorIso U M N).inv ≫
        (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
          (gammaU (X := X) U ((PresheafOfModules.tensorObj (O := (X).presheaf) (M.val) (N.val)))) :=
  Functor.map_comp _ _ _

/-- The morphism `deltaU U M N` is locally bijective. -/
theorem w_deltaU (M N : SheafOfModules.{u} (structureSheafRing X)) :
    ((JX X).over U).W
      ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map (deltaU (X := X) U M N)) := by
  rw [toPresheaf_map_deltaU]
  have : IsIso ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
      (resTensorIso (X := X) U M N).inv) :=
    ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).mapIso
      (resTensorIso (X := X) U M N).symm).isIso_hom
  exact ((JX X).over U).W.comp_mem _ _ ((((JX X).over U).W).of_isIso _) (w_gammaU U _)

/-- A morphism of sheaves of modules whose underlying morphism of presheaves of abelian groups
is locally bijective is an isomorphism. -/
theorem isIso_of_W {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.{u} R} (e : A ⟶ B)
    (he : J.W ((PresheafOfModules.toPresheaf R.obj).map e.val)) : IsIso e :=
  (isIso_iff_of_reflects_iso e (SheafOfModules.toSheaf R)).mp
    ((J.W_sheafToPresheaf_map_iff_isIso _).1 he)

/-- The canonical morphism from the tensor product, formed on the slice site at `U`, of the
restrictions of `M` and `N`, to the restriction of `M ⊗ N`. It is the morphism adjoint to
`deltaU`. -/
noncomputable def tensorOverHom (M N : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U), Presheaf.isSheaf_of_isSheaf_comp _
        ((OU (X := X) U)) (forget₂ CommRingCat RingCat) ((hOU U))⟩).obj ((ov U M))).obj ((ov U N)))
      ⟶
      ov U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
          (N))) :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (OU (X := X) U) (hOU U)).homEquiv
    ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U
      N).val)))
    (ov (X := X) U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
        (M)).obj (N))))).symm (deltaU (X := X) U M N)

/-- The sheafification unit followed by `tensorOverHom U M N` is `deltaU U M N`. -/
theorem toSheafify_comp_tensorOverHom (M N : SheafOfModules.{u} (structureSheafRing X)) :
    Stacks.SheafOfModules.TensorSheafification.toSheafify (OU (X := X) U) (hOU U)
        ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov
          U N).val))) ≫
      (SheafOfModules.forget (RU (X := X) U) ⋙
        PresheafOfModules.restrictScalars (𝟙 (RU (X := X) U).obj)).map
          (tensorOverHom (X := X) U M N)
      = deltaU (X := X) U M N :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (OU (X := X) U) (hOU
    U)).homEquiv_unit
      (f := tensorOverHom (X := X) U M N)).symm.trans
    (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (OU (X := X) U) (hOU
      U)).homEquiv _ _).apply_symm_apply _)

/-- The canonical morphism `tensorOverHom U M N` is an isomorphism. -/
instance isIso_tensorOverHom (M N : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (tensorOverHom (X := X) U M N) := by
  have hval : (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
        ((SheafOfModules.forget (RU (X := X) U) ⋙
          PresheafOfModules.restrictScalars (𝟙 (RU (X := X) U).obj)).map
            (tensorOverHom (X := X) U M N))
      = (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
          (tensorOverHom (X := X) U M N).val := rfl
  have hsplit : (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
        (Stacks.SheafOfModules.TensorSheafification.toSheafify (OU (X := X) U) (hOU U)
          ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U N).val)))) ≫
      (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
        (tensorOverHom (X := X) U M N).val
      = (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map (deltaU (X := X) U M N) :=
    hval ▸ ((Functor.map_comp (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)) _ _).symm.trans
      (congrArg (PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
        (toSheafify_comp_tensorOverHom (X := X) U M N)))
  have hηW : ((JX X).over U).W ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify (OU (X := X) U) (hOU U)
        ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov
          U N).val))))) := by
    change ((JX X).over U).W (CategoryTheory.toSheafify ((JX X).over U) _)
    exact ((JX X).over U).W_toSheafify _
  have hηIso := (((JX X).over U).W_iff _).mp hηW
  have hcompIso : IsIso ((presheafToSheaf ((JX X).over U) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
        (Stacks.SheafOfModules.TensorSheafification.toSheafify (OU (X := X) U) (hOU U)
          ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U N).val))))) ≫
      (presheafToSheaf ((JX X).over U) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
          (tensorOverHom (X := X) U M N).val)) := by
    rw [← Functor.map_comp, hsplit]
    exact (((JX X).over U).W_iff _).mp (w_deltaU (X := X) U M N)
  exact isIso_of_W _ ((((JX X).over U).W_iff _).2
    (IsIso.of_isIso_comp_left
      ((presheafToSheaf ((JX X).over U) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
          (Stacks.SheafOfModules.TensorSheafification.toSheafify (OU (X := X) U) (hOU U)
            ((PresheafOfModules.tensorObj (O := (OU (X := X) U)) ((ov U M).val) ((ov U N).val))))))
      ((presheafToSheaf ((JX X).over U) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf ((RU (X := X) U).obj)).map
          (tensorOverHom (X := X) U M N).val))))

/-- The restriction of `M ⊗_{O_X} N` to `U` is the tensor product, formed on the slice site at
`U`, of the restrictions of `M` and of `N`. -/
noncomputable def tensorOverIso (M N : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U), Presheaf.isSheaf_of_isSheaf_comp _
        ((OU (X := X) U)) (forget₂ CommRingCat RingCat) ((hOU U))⟩).obj ((ov U M))).obj ((ov U N)))
      ≅
      ov U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
          (N))) :=
  asIso (tensorOverHom (X := X) U M N)

/-! ### Tensoring by a locally trivial sheaf of modules -/

/-- Tensoring with the structure sheaf on the slice site is the identity. -/
noncomputable def tensorUnitRightIso (A : SheafOfModules.{u} (RU (X := X) U)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U), Presheaf.isSheaf_of_isSheaf_comp _
        ((OU (X := X) U)) (forget₂ CommRingCat RingCat) ((hOU U))⟩).obj (A)).obj
        ((SheafOfModules.unit (RU (X := X) U)))) ≅
      A := by
  letI : MonoidalCategory (PresheafOfModules.{u} (RU (X := X) U).obj) :=
    PresheafOfModules.monoidalCategory (R := OU (X := X) U)
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (OU (X := X) U) (hOU
    U)).counit := by
    change IsIso (PresheafOfModules.sheafificationAdjunction (𝟙 (RU (X := X) U).obj)).counit
    infer_instance
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify (OU (X := X) U) (hOU U)).mapIso (ρ_
    A.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (OU (X := X) U) (hOU
      U)).counit).app A

/-- Tensoring on the slice site is functorial in the second variable. -/
noncomputable def tensorSheafCongrRight (A : SheafOfModules.{u} (RU (X := X) U))
    {B B' : SheafOfModules.{u} (RU (X := X) U)} (θ : B ≅ B') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U), Presheaf.isSheaf_of_isSheaf_comp _
        ((OU (X := X) U)) (forget₂ CommRingCat RingCat) ((hOU U))⟩).obj (A)).obj (B)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U),
          Presheaf.isSheaf_of_isSheaf_comp _ ((OU (X := X) U)) (forget₂ CommRingCat RingCat)
          ((hOU U))⟩).obj (A)).obj (B')) := by
  letI : MonoidalCategory (PresheafOfModules.{u} (RU (X := X) U).obj) :=
    PresheafOfModules.monoidalCategory (R := OU (X := X) U)
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify (OU (X := X) U) (hOU U)).mapIso
    (whiskerLeftIso A.val ((SheafOfModules.forget (RU (X := X) U)).mapIso θ))

/-- If `N` restricts to the structure sheaf on `U`, then `M ⊗ N` restricts to `M` on `U`. -/
noncomputable def tensorOverIsoOfTrivial (M N : SheafOfModules.{u} (structureSheafRing X))
    (θ : N.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
        (N))).over U ≅ M.over U :=
  (tensorOverIso (X := X) U M N).symm ≪≫ tensorSheafCongrRight (X := X) U (ov U M) θ ≪≫
    tensorUnitRightIso (X := X) U (ov U M)

/-- The coherence predicates `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent`
agree. -/
theorem isCoherent_iff {Y : Type u} [TopologicalSpace Y]
    {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} (M : SheafOfModules.{u} R) :
    _root_.SheafOfModules.IsCoherent M ↔ Stacks.SheafOfModules.IsCoherent M :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The tensor product of a coherent sheaf of modules with a locally trivial one is coherent. -/
theorem isCoherent_tensorSheaf_of_isLocallyTrivial
    (M N : SheafOfModules.{u} (structureSheafRing X))
    (hM : _root_.SheafOfModules.IsCoherent M)
    (hN : Stacks.SheafOfModules.Invertible.IsLocallyTrivial N) :
    _root_.SheafOfModules.IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf,
        (X).IsSheaf⟩).obj (M)).obj (N))) := by
  have hMc : Stacks.SheafOfModules.IsCoherent M := (isCoherent_iff M).1 hM
  obtain ⟨I, W, hW, θ⟩ := hN.exists_trivializing_cover
  refine (isCoherent_iff _).2 (Stacks.SheafOfModules.isCoherent_of_coversTop _ W hW fun i => ?_)
  have ε := tensorOverIsoOfTrivial (X := X) (W i) M N (θ i).some
  have hMW : (M.over (W i)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_over_of_isFiniteType (W i)
  have hft : (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
      (N))).over (W i)).IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_iso _ _ _ _ _ _ _ _ _ ε.symm (by exact hMW)
  exact @Stacks.SheafOfModules.isCoherentOn_of_mono _ _ _ _ _ (by exact hMc) _ hft ε.hom
    (@IsIso.mono_of_iso _ _ _ _ ε.hom ε.isIso_hom)

/-! ### A factor of finite presentation and a coherent factor -/

section Cokernel

variable {C : Type u} [Category.{u} C] [Limits.HasFiniteWidePullbacks C]
  [Limits.HasBinaryProducts C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Z : C, HasSheafify (J.over Z) AddCommGrpCat.{u}]
  [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The pullback of a short exact sequence `S` with `S.X₁` of finite type along a morphism
`ψ : N ⟶ S.X₃`, where `N` has finitely many generating sections, is of finite type. -/
theorem isFiniteType_pullback_of_generatingSections
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) [S.X₁.IsFiniteType]
    {N : SheafOfModules.{u} R} (σ : N.GeneratingSections) [Finite σ.I] (ψ : N ⟶ S.X₃) :
    (Limits.pullback ψ S.g).IsFiniteType := by
  have hepi : Epi S.g := hS.epi_g
  have hmono : Mono S.f := hS.mono_f
  have hw : (0 : S.X₁ ⟶ N) ≫ ψ = S.f ≫ S.g := by rw [Limits.zero_comp, S.zero]
  have hzero : Limits.pullback.lift (0 : S.X₁ ⟶ N) S.f hw ≫ Limits.pullback.fst ψ S.g = 0 :=
    Limits.pullback.lift_fst _ _ _
  have hT : (ShortComplex.mk (Limits.pullback.lift (0 : S.X₁ ⟶ N) S.f hw)
      (Limits.pullback.fst ψ S.g) hzero).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isLimitKernelForkPullbackFst ψ S.g hS.fIsKernel _ hzero
          (Limits.pullback.lift_snd _ _ _))
      mono_f := mono_of_mono_fac (Limits.pullback.lift_snd (0 : S.X₁ ⟶ N) S.f hw)
      epi_g := inferInstance }
  exact isFiniteType_X₂_of_shortExact
    (S := ShortComplex.mk (Limits.pullback.lift (0 : S.X₁ ⟶ N) S.f hw)
      (Limits.pullback.fst ψ S.g) hzero) hT σ

end Cokernel

section CokernelSpace

variable {Y : Type u} [TopologicalSpace Y]
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- A sheaf of modules that is, on every open `W' ≤ W`, the cokernel of a morphism from a sheaf
of modules of finite type into the restriction of a coherent sheaf, is coherent on `W`. -/
theorem isCoherentOn_of_cokernel {M P : SheafOfModules.{u} R} [IsCoherent P] {W : Opens Y}
    (h : ∀ W' : Opens Y, W' ≤ W →
      ∃ (A : SheafOfModules.{u} (R.over W')) (f : A ⟶ P.over W'),
        A.IsFiniteType ∧ Nonempty (M.over W' ≅ Limits.cokernel f)) :
    IsCoherentOn M W := by
  intro W' hW'
  obtain ⟨A, f, hA, ⟨ε⟩⟩ := h W' hW'
  have hB : (P.over W').IsFiniteType := isFiniteType_over_of_isFiniteType W'
  have hcok : (Limits.cokernel f).IsFiniteType := isFiniteType_of_epi'.{u} (Limits.cokernel.π f)
  have hK : (Limits.kernel (Limits.cokernel.π f)).IsFiniteType :=
    isFiniteType_of_epi'.{u} (Abelian.factorThruImage f)
  refine ⟨isFiniteType_of_iso.{u} ε.symm, ?_⟩
  intro N σ hσ g
  have hS : (ShortComplex.kernelSequence (Limits.cokernel.π f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := inferInstanceAs (Epi (Limits.cokernel.π f)) }
  have hK' : (ShortComplex.kernelSequence (Limits.cokernel.π f)).X₁.IsFiniteType := hK
  have hQ : (Limits.pullback (g ≫ ε.hom) (Limits.cokernel.π f)).IsFiniteType :=
    isFiniteType_pullback_of_generatingSections
      (S := ShortComplex.kernelSequence (Limits.cokernel.π f)) hS σ (g ≫ ε.hom)
  have hj : Limits.pullback.lift (Limits.kernel.ι (g ≫ ε.hom))
      (0 : Limits.kernel (g ≫ ε.hom) ⟶ P.over W') (by simp) ≫
      Limits.pullback.snd (g ≫ ε.hom) (Limits.cokernel.π f) = 0 :=
    Limits.pullback.lift_snd _ _ _
  have hker : (Limits.kernel
      (Limits.pullback.snd (g ≫ ε.hom) (Limits.cokernel.π f))).IsFiniteType :=
    isFiniteType_kernel_over_of_isCoherent W'
      (Limits.pullback.snd (g ≫ ε.hom) (Limits.cokernel.π f))
  have hkg : (Limits.kernel (g ≫ ε.hom)).IsFiniteType :=
    isFiniteType_of_iso.{u}
      (M := Limits.kernel (Limits.pullback.snd (g ≫ ε.hom) (Limits.cokernel.π f)))
      (N := Limits.kernel (g ≫ ε.hom))
      (Limits.IsLimit.conePointUniqueUpToIso
        (Limits.kernelIsKernel (Limits.pullback.snd (g ≫ ε.hom) (Limits.cokernel.π f)))
        (isLimitKernelForkPullbackSnd (Limits.cokernel.π f)
          (hi := Limits.kernel.condition (g ≫ ε.hom))
          (Limits.kernelIsKernel (g ≫ ε.hom)) _ (Limits.pullback.lift_fst _ _ _) hj))
  exact isFiniteType_of_iso.{u} (Limits.kernelCompMono g ε.hom)

end CokernelSpace

/-! ### Tensoring on the left on the slice site -/

/-- Tensoring on the left by the restriction of `G` to the slice site at `U`. -/
noncomputable def tensorLeftOver (G : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (RU (X := X) U) ⥤ SheafOfModules.{u} (RU (X := X) U) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (J := ((JX X).over U)) ((X.sheaf.over U))).obj (ov U G)

/-- Tensoring on the left on the slice site preserves colimits. -/
noncomputable instance preservesColimitsOfSize_tensorLeftOver
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    Limits.PreservesColimitsOfSize.{u, u} (tensorLeftOver (X := X) U G) :=
  TensorColimits.tensorLeft_preservesColimits ((JX X).over U) (X.sheaf.over U) (ov U G)

/-- Tensoring on the left on the slice site preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorLeftOver
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    (tensorLeftOver (X := X) U G).PreservesZeroMorphisms := by
  have h0 : Limits.PreservesColimitsOfSize.{0, 0} (tensorLeftOver (X := X) U G) :=
    Limits.preservesColimitsOfSize_shrink _
  have h1 : Limits.PreservesColimit (Functor.empty.{0} _)
    (tensorLeftOver (X := X) U G) := inferInstance
  exact Functor.preservesZeroMorphisms_of_preserves_initial_object

/-- The value of `tensorLeftOver U G` at `A` is the slice-site tensor product `G|_U ⊗ A`. -/
noncomputable def tensorLeftOverObjIso (G : SheafOfModules.{u} (structureSheafRing X))
    (A : SheafOfModules.{u} (RU (X := X) U)) :
    (tensorLeftOver (X := X) U G).obj A ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(OU (X := X) U),
          Presheaf.isSheaf_of_isSheaf_comp _ ((OU (X := X) U)) (forget₂ CommRingCat RingCat)
          ((hOU U))⟩).obj ((ov U G))).obj (A)) :=
  Iso.refl _

/-- Tensoring the structure sheaf by `G|_U` gives `G|_U`. -/
noncomputable def tensorLeftOverUnitIso (G : SheafOfModules.{u} (structureSheafRing X)) :
    (tensorLeftOver (X := X) U G).obj (SheafOfModules.unit (RU (X := X) U)) ≅ ov U G :=
  tensorLeftOverObjIso (X := X) U G _ ≪≫ tensorUnitRightIso (X := X) U (ov U G)

/-- Tensoring the free sheaf of modules on `I` by `G|_U` gives the restriction of the coproduct
of `I` copies of `G`. -/
noncomputable def tensorLeftOverFreeIso (G : SheafOfModules.{u} (structureSheafRing X))
    (I : Type u) :
    (tensorLeftOver (X := X) U G).obj (SheafOfModules.free I) ≅
      ov U (∐ fun _ : I => G) :=
  Limits.PreservesCoproduct.iso (tensorLeftOver (X := X) U G)
      (fun _ : I => SheafOfModules.unit (RU (X := X) U)) ≪≫
    Limits.Sigma.mapIso (fun _ : I => tensorLeftOverUnitIso (X := X) U G) ≪≫
    (Limits.PreservesCoproduct.iso (SheafOfModules.overFunctor (structureSheafRing X) U)
      (fun _ : I => G)).symm

/-- Applying `tensorLeftOver U G` to a presentation of `F|_U` presents `(G ⊗ F)|_U` as a
cokernel. -/
noncomputable def cokernelTensorLeftOverIso
    (G F : SheafOfModules.{u} (structureSheafRing X)) (P : (F.over U).Presentation) :
    Limits.cokernel ((tensorLeftOver (X := X) U G).map
        ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
          Limits.kernel.ι P.generators.π))
      ≅ ov U ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (G)).obj
          (F))) :=
  (Limits.PreservesCokernel.iso (tensorLeftOver (X := X) U G)
      ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
        Limits.kernel.ι P.generators.π)).symm ≪≫
    (tensorLeftOver (X := X) U G).mapIso
      (P.isColimit.coconePointUniqueUpToIso (Limits.colimit.isColimit _)).symm ≪≫
    tensorLeftOverObjIso (X := X) U G (ov U F) ≪≫ tensorOverIso (X := X) U G F

/-- Precomposing and postcomposing with isomorphisms does not change a cokernel. -/
private noncomputable def cokernelIsoCompIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {W₁ W₂ Z₁ Z₂ : 𝒜} (e : W₁ ≅ W₂) (f : W₂ ⟶ Z₁) (e' : Z₁ ≅ Z₂) :
    Limits.cokernel (e.hom ≫ f ≫ e'.hom) ≅ Limits.cokernel f :=
  Limits.cokernelEpiComp e.hom (f ≫ e'.hom) ≪≫ Limits.cokernelCompIsIso f e'.hom

/-- If `F|_U` has a finite presentation and `G` is coherent, then `G ⊗ F` is coherent on `U`. -/
theorem isCoherentOn_tensorSheaf_of_presentation
    (G F : SheafOfModules.{u} (structureSheafRing X)) [IsCoherent G]
    (P : (F.over U).Presentation) [P.IsFinite] :
    IsCoherentOn ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
        (G)).obj (F))) U := by
  have hgen : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have hrel : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have hcohGen : IsCoherent (∐ fun _ : P.generators.I => G) := isCoherent_sigma _ fun _ => ‹_›
  have hcohRel : IsCoherent (∐ fun _ : P.relations.I => G) := isCoherent_sigma _ fun _ => ‹_›
  have hftRel : (∐ fun _ : P.relations.I => G).IsFiniteType := IsCoherent.isFiniteType
  refine isCoherentOn_of_cokernel (P := ∐ fun _ : P.generators.I => G) fun W' hW' => ?_
  let Q := LocalKernel.presentationOver (M := F) (homOfLE hW') P
  let f := (tensorLeftOver (X := X) W' G).map
    ((SheafOfModules.freeHomEquiv _).symm Q.relations.s ≫ Limits.kernel.ι Q.generators.π)
  exact ⟨ov W' (∐ fun _ : P.relations.I => G),
    (tensorLeftOverFreeIso (X := X) W' G P.relations.I).symm.hom ≫
      (f ≫ (tensorLeftOverFreeIso (X := X) W' G P.generators.I).hom),
    isFiniteType_over_of_isFiniteType W',
    ⟨(cokernelIsoCompIso (tensorLeftOverFreeIso (X := X) W' G P.relations.I).symm f
        (tensorLeftOverFreeIso (X := X) W' G P.generators.I) ≪≫
      cokernelTensorLeftOverIso (X := X) W' G F Q).symm⟩⟩

end Stacks.SheafOfModules.TensorOver

namespace AlgebraicGeometry.SheafOfModules

open AlgebraicGeometry
open Stacks.SheafOfModules.TensorOver (isCoherent_iff isCoherentOn_tensorSheaf_of_presentation)

/-- On a ringed space, the tensor product of a sheaf of modules of finite presentation with a
coherent sheaf of modules is coherent. -/
@[stacks 01CE "tensor_finite_presentation_coherent", instance]
theorem tensorSheaf_isCoherent_of_isFinitePresentation
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    [F.IsFinitePresentation] [_root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (F)).obj (G))) := by
  classical
  have hG : Stacks.SheafOfModules.IsCoherent G := (isCoherent_iff G).1 ‹_›
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  have hcov : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff X.carrier q.X).mp q.coversTop
  have hpt : ∀ x : X.carrier, ∃ i, x ∈ q.X i := fun x =>
    Set.mem_iUnion.mp (by simp [hcov.iSup_set_eq_univ] : x ∈ ⋃ i, (q.X i : Set X.carrier))
  choose idx hidx using hpt
  have hV : (Opens.grothendieckTopology X.carrier).CoversTop (fun x => q.X (idx x)) := by
    refine (Opens.coversTop_iff X.carrier _).2 (TopologicalSpace.IsOpenCover.mk ?_)
    ext y
    simpa using ⟨y, hidx y⟩
  have hGF : Stacks.SheafOfModules.IsCoherent
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (G)).obj
        (F))) :=
    Stacks.SheafOfModules.isCoherent_of_coversTop _ (fun x => q.X (idx x)) hV fun x =>
      have := hq.isFinite_presentation (idx x)
      isCoherentOn_tensorSheaf_of_presentation (q.X (idx x)) G F (q.presentation (idx x))
  exact (isCoherent_iff _).2 ((Stacks.SheafOfModules.coherentModules
    (structureSheafRing X)).prop_of_iso
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
        (structureSheafRing X).property G F) hGF)

/-- The tensor product of two coherent sheaves of modules is coherent. -/
@[stacks 01CE "tensor_coherent",
  stacks 01Y2 "tensor product",
  instance,
  ega "0 5.3.5" "tensor product", ega "I 9.1.1" "coherent tensor"]
theorem tensorSheaf_isCoherent (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (F)).obj (G))) :=
  have := isFinitePresentation_of_isCoherent F
  tensorSheaf_isCoherent_of_isFinitePresentation X F G

/-- On a scheme, the tensor product of a coherent sheaf of modules with an invertible one is
coherent. -/
theorem isCoherent_tensorSheaf_of_isInvertible (X : Scheme.{u}) (M N : X.Modules)
    [_root_.SheafOfModules.IsCoherent M] [IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (M)).obj
        (N))).IsCoherent := by
  have hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ N).2 ‹_›
  have : Stacks.SheafOfModules.Invertible.IsLocallyTrivial N :=
    Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible (X := X.toRingedSpace) N
  exact Stacks.SheafOfModules.TensorOver.isCoherent_tensorSheaf_of_isLocallyTrivial
    (X := X.toRingedSpace) M N ‹_› ‹_›

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

open CategoryTheory

/-- Every twist of a coherent sheaf of modules by invertible sheaves of modules is coherent. -/
theorem twistedSheaf_isCoherent {X : Scheme.{u}} {r : ℕ} (F : X.Modules) (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    [_root_.SheafOfModules.IsCoherent F] (n : Fin r → ℤ) :
    (twistedSheaf F L n).IsCoherent :=
  twistedSheaf_isCoherent_of_tensorSheaf_isCoherent F L n fun M N _ _ =>
    SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X M N

end AlgebraicGeometry

end
