module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitFreeModule
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Colimits of free sheaves of modules and of differential graded `(O, 0)`-modules

Three colimit statements used by the weight filtration of the source's proof of Tag 0FU1.

* The sheafification of the free `O`-module on a presheaf of sets, `F ↦ O[F]`, is a functor and
  preserves all colimits, being left adjoint to taking the underlying presheaf of sets.
* A cocone of right differential graded `(O, 0)`-modules is a colimit as soon as it is a colimit
  in every degree: forgetting to cochain complexes is fully faithful, so it reflects colimits,
  and colimits of complexes are computed degreewise.
* A directed union of subfunctors of a presheaf of sets is their colimit.

## Main definitions

* `SheafOfModules.freePieceFunctor`: `F ↦ O[F]` as a functor, with right adjoint
  `SheafOfModules.underlyingPresheafFunctor` (`SheafOfModules.freePieceAdjunction`).
* `SheafOfModules.subfunctorDiagram`, `SheafOfModules.subfunctorCocone` and
  `SheafOfModules.subfunctorCoconeTop`: the diagram of a monotone family of subfunctors and its
  cocones to an upper bound and to the ambient functor.

## Main results

* `SheafOfModules.isColimit_freePieceMapCocone`: `F ↦ O[F]` carries colimits to colimits.
* `SheafOfModules.DifferentialGradedModule.isColimitOfDegreewise`: a degreewise colimit of right
  differential graded `(O, 0)`-modules is a colimit.
* `SheafOfModules.isColimitSubfunctorUnion` and `SheafOfModules.isColimitSubfunctorUnionTop`: a
  directed union of subfunctors is a colimit.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

section FreePieceFunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

variable (Osharp) in
/-- The sheafification of the free `O`-module on a presheaf of sets, as a functor. -/
noncomputable def freePieceFunctor :
    (Cᵒᵖ ⥤ Type t) ⥤ SheafOfModules.{t} (toRingCat J Osharp) where
  obj F := freePieceOf Osharp F
  map φ := freePieceMap φ
  map_id F := freePieceMap_id F
  map_comp φ ψ := freePieceMap_comp φ ψ

/-- The functor `freePieceFunctor` sends `F` to `freePieceOf Osharp F`. -/
@[simp] theorem freePieceFunctor_obj (F : Cᵒᵖ ⥤ Type t) :
    (freePieceFunctor Osharp).obj F = freePieceOf Osharp F := rfl

/-- The functor `freePieceFunctor` sends `φ` to `freePieceMap φ`. -/
@[simp] theorem freePieceFunctor_map {F G : Cᵒᵖ ⥤ Type t} (φ : F ⟶ G) :
    (freePieceFunctor Osharp).map φ = freePieceMap φ := rfl

variable (Osharp) in
/-- The underlying presheaf of sets of a sheaf of modules, as a functor. -/
noncomputable def underlyingPresheafFunctor :
    SheafOfModules.{t} (toRingCat J Osharp) ⥤ (Cᵒᵖ ⥤ Type t) where
  obj M := M.val.presheaf ⋙ CategoryTheory.forget _
  map g := Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map g.val)
    (CategoryTheory.forget _)

omit [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- On sections, the image of `g` under `underlyingPresheafFunctor` acts as `g`. -/
@[simp] theorem underlyingPresheafFunctor_map_app {M N : SheafOfModules.{t} (toRingCat J Osharp)}
    (g : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((underlyingPresheafFunctor Osharp).map g).app U x = g.val.app U x := rfl

/-- Morphisms out of `O[F]` are morphisms of presheaves of sets out of `F`. -/
noncomputable def freePieceHomEquiv (F : Cᵒᵖ ⥤ Type t)
    (M : SheafOfModules.{t} (toRingCat J Osharp)) :
    (freePieceOf Osharp F ⟶ M) ≃ (F ⟶ (underlyingPresheafFunctor Osharp).obj M) where
  toFun g := freeGenNat Osharp F ≫ (underlyingPresheafFunctor Osharp).map g
  invFun φ := freePieceDesc M φ
  left_inv g := freePieceOf_hom_ext fun U p =>
    freePieceDesc_gen M (freeGenNat Osharp F ≫ (underlyingPresheafFunctor Osharp).map g) p
  right_inv φ := by
    ext U p
    exact freePieceDesc_gen M φ p

/-- The morphism of presheaves of sets attached to `g : O[F] ⟶ M` sends a section `p` of `F` to
the image under `g` of the generator `freeGen Osharp p`. -/
theorem freePieceHomEquiv_apply_app (F : Cᵒᵖ ⥤ Type t)
    (M : SheafOfModules.{t} (toRingCat J Osharp)) (g : freePieceOf Osharp F ⟶ M) (U : Cᵒᵖ)
    (p : F.obj U) : (freePieceHomEquiv F M g).app U p = g.val.app U (freeGen Osharp p) := rfl

variable (Osharp) in
/-- **`F ↦ O[F]` is left adjoint to taking the underlying presheaf of sets.** -/
noncomputable def freePieceAdjunction :
    freePieceFunctor Osharp ⊣ underlyingPresheafFunctor (J := J) Osharp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F M => freePieceHomEquiv F M
      homEquiv_naturality_left_symm := fun {F G M} φ ψ => by
        refine freePieceOf_hom_ext fun U p => ?_
        change (freePieceDesc M (φ ≫ ψ)).val.app U (freeGen Osharp p) =
          (freePieceDesc M ψ).val.app U ((freePieceMap φ).val.app U (freeGen Osharp p))
        rw [freePieceMap_gen]
        exact (freePieceDesc_gen M (φ ≫ ψ) p).trans (freePieceDesc_gen M ψ (φ.app U p)).symm
      homEquiv_naturality_right := fun {F M N} g h => rfl }

/-- The functor `F ↦ O[F]` is a left adjoint. -/
instance : (freePieceFunctor Osharp (J := J)).IsLeftAdjoint :=
  (freePieceAdjunction Osharp).isLeftAdjoint

/-- **`F ↦ O[F]` carries colimits of presheaves of sets to colimits of sheaves of modules.** -/
noncomputable def isColimit_freePieceMapCocone {K : Type t} [SmallCategory K]
    {G : K ⥤ (Cᵒᵖ ⥤ Type t)} {c : Cocone G} (hc : IsColimit c) :
    IsColimit ((freePieceFunctor Osharp).mapCocone c) :=
  have : PreservesColimitsOfSize.{t, t} (freePieceFunctor Osharp (J := J)) :=
    (freePieceAdjunction Osharp (J := J)).leftAdjoint_preservesColimits
  isColimitOfPreserves (freePieceFunctor Osharp) hc

end FreePieceFunctor

section Degreewise

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

/-- **A cocone of right differential graded `(O, 0)`-modules which is a colimit in every degree
is a colimit.** Forgetting to cochain complexes is fully faithful, hence reflects colimits, and a
cocone of cochain complexes which is a colimit in every degree is a colimit. -/
noncomputable def DifferentialGradedModule.isColimitOfDegreewise {K : Type t} [SmallCategory K]
    {F : K ⥤ DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)} (c : Cocone F)
    (hc : ∀ n : ℤ, IsColimit ((toCochainComplex.{t, t, m} (unitDGAlgebra Osharp) ⋙
      HomologicalComplex.eval _ _ n).mapCocone c)) : IsColimit c :=
  isColimitOfReflects (toCochainComplex.{t, t, m} (unitDGAlgebra Osharp))
    (HomologicalComplex.isColimitOfEval _ _ fun n => hc n)

end Degreewise

section Subfunctors

variable {D : Type u} [Category.{v} D] {X : D ⥤ Type t}

/-- The diagram of a monotone family of subfunctors indexed by a preorder. -/
def subfunctorDiagram {K : Type t} [Preorder K] (S : K → Subfunctor X) (hmono : Monotone S) :
    K ⥤ (D ⥤ Type t) where
  obj k := (S k).toFunctor
  map {k k'} h := Subfunctor.homOfLe (hmono (leOfHom h))

/-- The cocone of a monotone family of subfunctors to a subfunctor containing all of them. -/
def subfunctorCocone {K : Type t} [Preorder K] (S : K → Subfunctor X) (hmono : Monotone S)
    (T : Subfunctor X) (hle : ∀ k, S k ≤ T) : Cocone (subfunctorDiagram S hmono) where
  pt := T.toFunctor
  ι := { app := fun k => Subfunctor.homOfLe (hle k) }

/-- **A directed union of subfunctors is their colimit.** -/
noncomputable def isColimitSubfunctorUnion {K : Type t} [Preorder K] [IsDirected K (· ≤ ·)]
    [Nonempty K] (S : K → Subfunctor X) (T : Subfunctor X) (hmono : Monotone S)
    (hle : ∀ k, S k ≤ T) (hcov : ∀ (U : D) (x : X.obj U), x ∈ T.obj U → ∃ k, x ∈ (S k).obj U) :
    IsColimit (subfunctorCocone S hmono T hle) := by
  refine evaluationJointlyReflectsColimits _ fun U => ?_
  refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_)
  · obtain ⟨k, hk⟩ := hcov U x.1 x.2
    exact ⟨k, ⟨x.1, hk⟩, rfl⟩
  · obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    have h' : xi.1 = xj.1 := congrArg Subtype.val h
    exact Subtype.ext h'

/-- The cocone of a monotone family of subfunctors to the ambient functor. -/
def subfunctorCoconeTop {K : Type t} [Preorder K] (S : K → Subfunctor X) (hmono : Monotone S) :
    Cocone (subfunctorDiagram S hmono) where
  pt := X
  ι := { app := fun k => (S k).ι }

/-- **A directed family of subfunctors exhausting a presheaf of sets has it as its colimit.** -/
noncomputable def isColimitSubfunctorUnionTop {K : Type t} [Preorder K] [IsDirected K (· ≤ ·)]
    [Nonempty K] (S : K → Subfunctor X) (hmono : Monotone S)
    (hcov : ∀ (U : D) (x : X.obj U), ∃ k, x ∈ (S k).obj U) :
    IsColimit (subfunctorCoconeTop S hmono) := by
  refine evaluationJointlyReflectsColimits _ fun U => ?_
  refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_)
  · obtain ⟨k, hk⟩ := hcov U x
    exact ⟨k, ⟨x, hk⟩, rfl⟩
  · obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨k, homOfLE hik, homOfLE hjk, Subtype.ext h⟩

end Subfunctors

end SheafOfModules

end
