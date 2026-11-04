module

public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DirectSums
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Eilenberg–Watts comparison at a flat module over a principal ideal domain

Let `R` be a principal ideal domain and `F : ModuleCat R ⥤ ModuleCat R` an `R`-linear functor.
The comparison map `F(R) ⊗[R] M ⟶ F(M)` of `Stacks.EilenbergWatts.wattsMap` is an isomorphism at
every flat `R`-module `M`, as soon as `F` commutes with the filtered colimit of the finitely
generated submodules of `M`.

A flat module over a domain is torsion free, a finitely generated torsion free module over a
principal ideal domain is free of finite rank, and every module is the filtered colimit of its
finitely generated submodules. On a free module of finite rank the comparison is invertible by
additivity (`Stacks.EilenbergWatts.isIso_wattsMap_of_basis`), and the filtered colimit is
transported by `Stacks.EilenbergWatts.isIso_app_of_isColimit`. This is the trade against
`Stacks.EilenbergWatts.isIso_wattsMap`: no right exactness of `F` is required, only one filtered
colimit, and in exchange the module is required to be flat.

## Main definitions

* `Stacks.EilenbergWatts.FGSub`: the finitely generated submodules of a module, as a filtered
  index category, with the diagram `fgDiagram` and the cocone `fgCocone` of inclusions.
* `Stacks.EilenbergWatts.fgCoconeIsColimit`: a module is the colimit of its finitely generated
  submodules.

## Main results

* `Stacks.EilenbergWatts.isIso_wattsMap_of_flat`: the comparison is invertible at a flat module.
* `Stacks.EilenbergWatts.wattsMap_natTrans`: the comparison is natural in the functor.
* `Stacks.EilenbergWatts.linear_uliftInt`: over a universe-lifted copy of `ℤ` every additive
  functor between linear categories is linear, so the hypothesis `F.Linear R` is automatic there.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E), steps 7 and 8 of the
  proof.
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.EilenbergWatts

/-! ### A module is the filtered colimit of its finitely generated submodules -/

section FG

variable {R : Type u} [CommRing R]

/-- The poset of finitely generated submodules of a module, as an index category. -/
abbrev FGSub (M : ModuleCat.{u} R) := {N : Submodule R M // N.FG}

/-- The finitely generated submodules of a module are directed: two of them lie in their sum. -/
instance (M : ModuleCat.{u} R) : IsDirectedOrder (FGSub M) where
  directed A B := ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, le_sup_left, le_sup_right⟩

/-- A module has a finitely generated submodule, namely `⊥`. -/
instance (M : ModuleCat.{u} R) : Nonempty (FGSub M) := ⟨⟨⊥, Submodule.fg_bot⟩⟩

/-- The finitely generated submodules of a module form a filtered category. -/
instance (M : ModuleCat.{u} R) : IsFiltered (FGSub M) := isFiltered_of_directed_le_nonempty _

/-- The diagram of the finitely generated submodules of `M`, with the inclusions as transition
maps. -/
def fgDiagram (M : ModuleCat.{u} R) : FGSub M ⥤ ModuleCat.{u} R where
  obj N := ModuleCat.of R N.1
  map h := ModuleCat.ofHom (Submodule.inclusion (leOfHom h))

/-- The cocone on `fgDiagram M` given by the inclusions of the finitely generated submodules. -/
def fgCocone (M : ModuleCat.{u} R) : Cocone (fgDiagram M) where
  pt := M
  ι := { app := fun N => ModuleCat.ofHom N.1.subtype
         naturality _ _ _ := rfl }

/-- The value of a cocone leg on an element does not depend on the finitely generated submodule
containing it at which the leg is taken. -/
theorem fgCocone_app_apply_eq {M : ModuleCat.{u} R} (t : Cocone (fgDiagram M)) (B C : FGSub M)
    (x : M) (hB : x ∈ B.1) (hC : x ∈ C.1) :
    (t.ι.app B).hom ⟨x, hB⟩ = (t.ι.app C).hom ⟨x, hC⟩ := by
  have key : ∀ (P Q : FGSub M) (h : P ≤ Q) (y : M) (hP : y ∈ P.1),
      (t.ι.app P).hom ⟨y, hP⟩ = (t.ι.app Q).hom ⟨y, h hP⟩ := fun P Q h y hP =>
    (congrArg (fun φ => φ.hom (⟨y, hP⟩ : P.1)) (t.w (homOfLE h))).symm
  rw [key B ⟨B.1 ⊔ C.1, B.2.sup C.2⟩ le_sup_left x hB,
    key C ⟨B.1 ⊔ C.1, B.2.sup C.2⟩ le_sup_right x hC]

/-- The map out of `M` induced by a cocone on its finitely generated submodules: an element is
sent to the value of the leg at the submodule it generates. -/
def fgDesc {M : ModuleCat.{u} R} (t : Cocone (fgDiagram M)) : M ⟶ t.pt :=
  ModuleCat.ofHom
    { toFun := fun x =>
        (t.ι.app ⟨R ∙ x, Submodule.fg_span_singleton x⟩).hom
          ⟨x, Submodule.mem_span_singleton_self x⟩
      map_add' := fun x y => by
        have hx : x ∈ (R ∙ x) ⊔ (R ∙ y) :=
          Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
        have hy : y ∈ (R ∙ x) ⊔ (R ∙ y) :=
          Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
        let C : FGSub M := ⟨(R ∙ x) ⊔ (R ∙ y),
          (Submodule.fg_span_singleton x).sup (Submodule.fg_span_singleton y)⟩
        rw [fgCocone_app_apply_eq t _ C (x + y) _ (add_mem hx hy),
          fgCocone_app_apply_eq t _ C x _ hx, fgCocone_app_apply_eq t _ C y _ hy]
        exact map_add (t.ι.app C).hom (⟨x, hx⟩ : C.1) ⟨y, hy⟩
      map_smul' := fun r x => by
        have hx : x ∈ R ∙ x := Submodule.mem_span_singleton_self x
        let C : FGSub M := ⟨R ∙ x, Submodule.fg_span_singleton x⟩
        rw [fgCocone_app_apply_eq t _ C (r • x) _ (Submodule.smul_mem _ r hx)]
        exact map_smul (t.ι.app C).hom r (⟨x, hx⟩ : C.1) }

/-- **A module is the filtered colimit of its finitely generated submodules.** -/
def fgCoconeIsColimit (M : ModuleCat.{u} R) : IsColimit (fgCocone M) where
  desc t := fgDesc t
  fac t N := by
    ext x
    exact fgCocone_app_apply_eq t _ N x.1 _ x.2
  uniq _ _ hm := by
    ext x
    exact congrArg (fun φ => φ.hom (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x))
      (hm ⟨R ∙ x, Submodule.fg_span_singleton x⟩)

end FG

/-! ### Flat modules over a principal ideal domain -/

section Flat

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [F.Linear R]

/-- **The comparison is invertible at a finitely generated torsion free module** over a
principal ideal domain: such a module is free of finite rank, and `F`, being additive, preserves
finite direct sums. -/
theorem isIso_wattsMap_of_finite_isTorsionFree (N : ModuleCat.{u} R) [Module.Finite R N]
    [Module.IsTorsionFree R N] : IsIso (wattsMap F N) := by
  classical
  let b := (Module.Free.chooseBasis R N).reindex
    ((Fintype.equivFin (Module.Free.ChooseBasisIndex R N)).trans Equiv.ulift.symm)
  exact isIso_wattsMap_of_basis F N b inferInstance

/-- **The Eilenberg–Watts comparison is an isomorphism at a flat module over a principal ideal
domain**, for a linear functor commuting with the filtered colimit of the finitely generated
submodules of that module. A flat module over a domain is torsion free; its finitely generated
submodules are therefore free of finite rank, where the comparison is invertible, and the module
is their filtered colimit. -/
theorem isIso_wattsMap_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (hF : PreservesColimitsOfShape (FGSub M) F) : IsIso (wattsMap F M) := by
  have := hF
  have : Module.IsTorsionFree R M :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr Module.Flat.torsion_eq_bot
  refine isIso_app_of_isColimit (wattsNatTrans F) (fgCoconeIsColimit M) (fun P => ?_)
  have : Module.Finite R P.1 := Module.Finite.iff_fg.mpr P.2
  exact isIso_wattsMap_of_finite_isTorsionFree F (ModuleCat.of R P.1)

end Flat

/-! ### Naturality in the functor -/

section Naturality

variable {R : Type u} [CommRing R]
  {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]

/-- **The Eilenberg–Watts comparison is natural in the functor**: a natural transformation
`θ : F ⟶ G` commutes with the two comparison maps, `θ_R ⊗ M` being the map on the sources. -/
theorem wattsMap_natTrans (θ : F ⟶ G) (M : ModuleCat.{u} R) :
    wattsMap F M ≫ θ.app M = (θ.app (ModuleCat.of R R) ▷ M) ≫ wattsMap G M := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x m => ?_)
  change (θ.app M).hom ((F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x) =
    (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom ((θ.app _).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, θ.naturality]

end Naturality

/-! ### Linearity over the lifted integers -/

/-- **Over the lifted integers every additive functor between linear categories is linear**:
multiplication by a lifted integer on a group of morphisms is an integer multiple, which an
additive functor preserves. -/
theorem linear_uliftInt {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear (ULift.{u} ℤ) C] [Linear (ULift.{u} ℤ) D] (G : C ⥤ D) [G.Additive] :
    G.Linear (ULift.{u} ℤ) where
  map_smul {X Y} f r := by
    obtain ⟨n⟩ := r
    have e : (ULift.up n : ULift.{u} ℤ) = ((n : ℤ) : ULift.{u} ℤ) := by
      ext
      simp
    rw [e, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, G.map_zsmul]

end Stacks.EilenbergWatts

end
