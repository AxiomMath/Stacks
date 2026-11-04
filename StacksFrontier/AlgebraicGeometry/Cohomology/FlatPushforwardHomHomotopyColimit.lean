module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlatPushforwardSectionsHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Cohomology.PerfectTwistSheafHomDual
import StacksCore.Tactic.StacksAttribute

/-!
# `RΓ(U, Lf^* K) = hocolim R Hom_X(Lₙ, K)` for `f` flat of finite presentation

Let `A` be a ring, `X` a scheme of finite presentation over `A` and `f : U ⟶ X` a flat morphism
of finite presentation. Part (1) of [Stacks, Tag 0CRR]: there is an inverse system `Lₙ` of
perfect objects of `D(𝒪_X)` with

`RΓ(U, Lf^* K) = hocolim R Hom_X(Lₙ, K) = hocolim RΓ(X, R𝓗om(Lₙ, K))`

in `D(A)`, functorially in `K` in `D_QCoh(𝒪_X)`.

## Main results

* `CategoryTheory.Pretriangulated.IsHomotopyColimitWith.ofIsoSystem`: a derived colimit of a
  system is one of every isomorphic system.
* `exists_isHomotopyColimitWith_derivedGlobalSectionsOver_derivedSheafHom` (in the namespace
  `Stacks.Cohomology.CountableSections`): [Stacks, Tag 0CRR], part (1).

## Implementation notes

Part (2), biduality and the identification of Tag 08DQ exist only at `HasDerivedCategory.standard`,
so part (1) is stated there, with the model scoped to the declaration.

## References

* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe u

/-! ### Derived colimits along an isomorphism of systems -/

/-- **A derived colimit of an isomorphic system.** If `K = hocolim Gₙ` with coprojections `cₙ`
and `e : F ≅ G` is an isomorphism of systems, then `K = hocolim Fₙ` with coprojections
`eₙ ≫ cₙ`. -/
theorem CategoryTheory.Pretriangulated.IsHomotopyColimitWith.ofIsoSystem {D : Type*}
    [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕ ⥤ D} [HasCoproduct F.obj] [HasCoproduct G.obj] {K : D} {c : ∀ n, G.obj n ⟶ K}
    (e : F ≅ G) (h : IsHomotopyColimitWith G K c) :
    IsHomotopyColimitWith F K (fun n => e.hom.app n ≫ c n) := by
  obtain ⟨p, q, hT, hc⟩ := h
  let σ : ∐ F.obj ≅ ∐ G.obj :=
    { hom := Limits.Sigma.desc fun n => e.hom.app n ≫ Limits.Sigma.ι G.obj n
      inv := Limits.Sigma.desc fun n => e.inv.app n ≫ Limits.Sigma.ι F.obj n
      hom_inv_id := Limits.Sigma.hom_ext _ _ fun n => by simp
      inv_hom_id := Limits.Sigma.hom_ext _ _ fun n => by simp }
  refine ⟨σ.hom ≫ p, q ≫ (shiftFunctor D (1 : ℤ)).map σ.inv,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ σ σ (Iso.refl _) ?_ ?_ ?_), fun n => ?_⟩
  · refine Limits.Sigma.hom_ext _ _ fun n => ?_
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, σ,
      Limits.Sigma.ι_desc_assoc, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      Limits.Sigma.ι_desc]
    rw [← NatTrans.naturality_assoc]
  · simp
  · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.refl_hom,
      Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · simp [σ, ← hc n]

namespace Stacks.Cohomology.CountableSections

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
  Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

section Tag

variable {A : Type u} [CommRing A] {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) (f : U ⟶ X)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- Let `A` be a ring, `X` a scheme of finite presentation over `A` (`p : X ⟶ Spec A`) and
`f : U ⟶ X` flat of finite presentation. There are an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of perfect
objects and maps

`dₙ : RΓ(X, R𝓗om(Lₙ, -)) ⟶ RΓ(U, Lf^* -)`

of functors `D(𝒪_X) ⥤ D(A)`, compatible with the transition maps, such that for every `K` in
`D_QCoh(𝒪_X)` the maps `dₙ` at `K` exhibit

`RΓ(U, Lf^* K) = hocolim RΓ(X, R𝓗om(Lₙ, K)) = hocolim R Hom_X(Lₙ, K)`

in `D(A)`. The system `L` and the maps `dₙ` do not depend on `K`, and `dₙ` is natural in `K`:
this is the source's "functorially in `K` in `D_QCoh(𝒪_X)`". Here `RΓ(X, -)` is the derived
global sections functor into `D(A)`, `R𝓗om` the derived internal Hom, `Lf^*` the derived pullback
of [Stacks, Tag 06YJ], and `hocolim` the derived colimit of [Stacks, Tag 090Z].

Stated at `HasDerivedCategory.standard`, scoped to this declaration: part (2), biduality and
[Stacks, Tag 08DQ] exist only at that model. -/
@[stacks 0CRR "(1)"]
theorem exists_isHomotopyColimitWith_derivedGlobalSectionsOver_derivedSheafHom
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
      (d : ∀ n, (Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op (L.obj (op n))) ⋙
          derivedGlobalSectionsOver p ⟶
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
          derivedGlobalSectionsOver (f ≫ p)),
      (∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (L.obj (op n))) ∧
      (∀ n, Functor.whiskerRight ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          (L.map (homOfLE (Nat.le_succ n)).op).op) (derivedGlobalSectionsOver p) ≫ d (n + 1) =
          d n) ∧
      ∀ K : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
        IsHomotopyColimitWith
          (L.rightOp ⋙ (Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj K ⋙
            derivedGlobalSectionsOver p)
          ((derivedGlobalSectionsOver (f ≫ p)).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              f.toLRSHom.toShHom).obj K))
          (fun n => (d n).app K) := by
  obtain ⟨E, c, hEp, hcomp, hcolim⟩ :=
    exists_isHomotopyColimitWith_derivedGlobalSectionsOver_derivedTensor p f
  let T := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf
  let Γ := derivedGlobalSectionsOver p
  let O := RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)
  let L : ℕᵒᵖ ⥤ DerivedCategory X.Modules :=
    E.op ⋙ (Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj O
  have hEs : ∀ n, (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect (E.obj n) := fun n =>
    Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace
      (E.obj n) (hEp n)
  let ψ := fun n => schemeDerivedTensorIsoSheafHomDual X (E.obj n) (hEs n)
  have hψ : ∀ {n m : ℕ} (g : n ⟶ m) (K : DerivedCategory X.Modules),
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map (L.map g.op).op).app K ≫
          (ψ m).inv.app K = (ψ n).inv.app K ≫ (T.obj K).map (E.map g) := by
    intro n m g K
    have h := schemeDerivedTensorIsoSheafHomDual_hom_naturality X (E.map g) (hEs n) (hEs m) K
    exact ((ψ n).inv_hom_id_app_assoc K _).symm.trans (congrArg ((ψ n).inv.app K ≫ ·)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (ψ m).inv.app K) h.symm).trans
        ((Category.assoc _ _ _).trans ((congrArg _ ((ψ m).hom_inv_id_app K)).trans
          (Category.comp_id _))))))
  refine ⟨L, fun n => Functor.whiskerRight (ψ n).inv Γ ≫ c n, fun n =>
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace (E.obj n)
      (hEp n), fun n => ?_, fun K hK => ?_⟩
  · have hnat : (Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          (L.map (homOfLE (Nat.le_succ n)).op).op ≫ (ψ (n + 1)).inv =
        (ψ n).inv ≫ T.flip.map (E.map (homOfLE (Nat.le_succ n))) := by
      ext K
      exact hψ (homOfLE (Nat.le_succ n)) K
    have h1 := (Functor.whiskerRight_comp _ _ Γ).symm.trans
      ((congrArg (fun t => Functor.whiskerRight t Γ) hnat).trans
        (Functor.whiskerRight_comp _ _ Γ))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c (n + 1)) h1).trans
      ((Category.assoc _ _ _).trans (congrArg _ (hcomp n))))
  · have h := hcolim K hK
    let e : L.rightOp ⋙ (Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj K ⋙ Γ ≅
        E ⋙ T.obj K ⋙ Γ :=
      NatIso.ofComponents (fun n => Γ.mapIso ((ψ n).app K).symm) fun {n m} g =>
        (Γ.map_comp _ _).symm.trans ((congrArg Γ.map (hψ g K)).trans (Γ.map_comp _ _))
    exact (IsHomotopyColimitWith.ofIsoSystem e h).congr_coprojections fun n => rfl

end Tag

end Stacks.Cohomology.CountableSections

end
