module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomInjectiveHomology
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityBiduality

/-!
# Local duality in Matlis form, naturally

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a Noetherian ring `A`, let `Z = V(I)`,
let `ω` be a dualizing complex and let `E` be an `A`-module together with an identification
`θ : RΓ_Z(ω) ≅ E[0]`. For every `K` bounded below with finite cohomology modules there is an
`A`-linear isomorphism

`H^n_Z(K) ≅ Hom_A(Ext^{-n}_A(K, ω), E)`

and it is **natural in `K`**: the square against the two maps induced by a morphism `K ⟶ K'`
commutes. Over a Noetherian local ring with a normalized dualizing complex, `θ` exists with `E`
an injective hull of the residue field, by Stacks 0A82; that is the Matlis form of Stacks 0AAK,
with no completion on either side.

Two statements compose, and both are natural in `K`:

* `Dualizing.LocalDuality.localCohomologyBidualityMor` with its naturality — local duality in
  the derived category, `RΓ_Z(K) ≅ RHom_A(RHom_A(K, ω), RΓ_Z(ω))`;
* `Dualizing.homologyDerivedHomInjectiveEquiv` with its naturality — the degree-`n` cohomology
  of `RHom_A(-, E[0])` is the dual of the degree-`(-n)` cohomology.

## Main definitions

* `Dualizing.LocalDuality.localDualityMor` — the canonical morphism
  `RΓ_Z(K) ⟶ RHom_A(RHom_A(K, ω), E[0])`, which is `θ` applied to local duality.
* `Dualizing.LocalDuality.localDualityMatlisEquiv` — the isomorphism
  `H^n_Z(K) ≅ Hom_A(Ext^{-n}_A(K, ω), E)`.

## Main results

* `Dualizing.LocalDuality.localDualityMor_naturality` and
  `Dualizing.LocalDuality.isIso_localDualityMor`.
* `Dualizing.LocalDuality.localDualityMatlisEquiv_comp` — **the naturality of the Matlis form**,
  in exactly the shape that `Stacks.Algebraization.MatlisDualModel.dualEquiv_comp` asks for.

## References

* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom
open Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing.LocalDuality

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}
  (I : Ideal A) (hI : I.FG) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
  (ω : DerivedCategory (ModuleCat.{u} A)) (E : ModuleCat.{u} A)
  (θ : (localCohomologyEndofunctor A I hI).obj ω ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)

/-- **Local duality with the target read through `θ`.** The canonical morphism
`RΓ_Z(K) ⟶ RHom_A(RHom_A(K, ω), E[0])`: local duality in the derived category followed by `θ`
in the second argument of the outer derived Hom. -/
def localDualityMor (K : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyEndofunctor A I hI).obj K ⟶
      (derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)),
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) :=
  localCohomologyBidualityMor I hI f hf ω K ≫
    ((derivedHomAdjunction (R := A)).hom.mapIso ((Iso.refl _).prod θ)).hom

omit [IsNoetherianRing A] in
/-- `Dualizing.LocalDuality.localDualityMor` is natural in `K`. The first factor is
`Dualizing.LocalDuality.localCohomologyBidualityMor_naturality`; the second is `RHom` of a
morphism in the other variable, which commutes with it by bifunctoriality. -/
theorem localDualityMor_naturality {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ K') :
    (localCohomologyEndofunctor A I hI).map g ≫ localDualityMor I hI f hf ω E θ K' =
      localDualityMor I hI f hf ω E θ K ≫
        (derivedHomAdjunction (R := A)).hom.map
          ((((derivedHomAdjunction (R := A)).hom.map
            ((g.op, 𝟙 ω) : ((Opposite.op K', ω) : _ × _) ⟶ (Opposite.op K, ω))).op,
              𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) : _ ⟶ _) := by
  have hpair : ((((derivedHomAdjunction (R := A)).hom.map
          ((g.op, 𝟙 ω) : ((Opposite.op K', ω) : _ × _) ⟶ (Opposite.op K, ω))).op,
        𝟙 ((localCohomologyEndofunctor A I hI).obj ω)) : _ ⟶ _) ≫
      ((Iso.refl (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K', ω)))).prod θ).hom =
      ((Iso.refl (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op K, ω)))).prod θ).hom ≫
        ((((derivedHomAdjunction (R := A)).hom.map
            ((g.op, 𝟙 ω) : ((Opposite.op K', ω) : _ × _) ⟶ (Opposite.op K, ω))).op,
          𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) : _ ⟶ _) := by
    refine Prod.ext ?_ ?_ <;> simp
  dsimp only [localDualityMor, Functor.mapIso_hom]
  rw [← Category.assoc, localCohomologyBidualityMor_naturality]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hpair]

/-- `Dualizing.LocalDuality.localDualityMor` is invertible for `ω` dualizing and `K` bounded
below with finite cohomology modules: this is
`Dualizing.LocalDuality.isIso_localCohomologyBidualityMor` followed by an isomorphism. -/
theorem isIso_localDualityMor (K : DerivedCategory (ModuleCat.{u} A))
    (hω : IsDualizingComplex ω) (m : ℤ) (hKge : K.IsGE m)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    IsIso (localDualityMor I hI f hf ω E θ K) := by
  have := isIso_localCohomologyBidualityMor I hI f hf ω K hω m hKge hK
  rw [localDualityMor]
  infer_instance

/-- **Local duality in Matlis form.** `H^n_Z(K) ≅ Hom_A(Ext^{-n}_A(K, ω), E)`, `A`-linearly.
Naturality in `K` is `Dualizing.LocalDuality.localDualityMatlisEquiv_comp`. -/
def localDualityMatlisEquiv [Injective E] (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hiso : IsIso (localDualityMor I hI f hf ω E θ K)) :
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((localCohomologyEndofunctor A I hI).obj K) : Type u)) ≃ₗ[A]
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n)).obj
          ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)) : Type u) →ₗ[A]
        (E : Type u)) :=
  (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      (@asIso _ _ _ _ _ hiso)).toLinearEquiv).trans
    (homologyDerivedHomInjectiveEquiv
      ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)) E n)

omit [IsNoetherianRing A] in
/-- **The Matlis form of local duality is natural in `K`.** For `g : K ⟶ K'`, the isomorphism at
`K'` composed with the map induced on local cohomology is the isomorphism at `K` composed with
the map induced on `Ext`. This is the shape of
`Stacks.Algebraization.MatlisDualModel.dualEquiv_comp`. -/
theorem localDualityMatlisEquiv_comp [Injective E] (n : ℤ)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ K')
    (hiso : IsIso (localDualityMor I hI f hf ω E θ K))
    (hiso' : IsIso (localDualityMor I hI f hf ω E θ K'))
    (x : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((localCohomologyEndofunctor A I hI).obj K) : Type u)) :
    localDualityMatlisEquiv I hI f hf ω E θ n K' hiso'
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((localCohomologyEndofunctor A I hI).map g)).hom x) =
      (localDualityMatlisEquiv I hI f hf ω E θ n K hiso x).comp
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n)).map
          ((derivedHomAdjunction (R := A)).hom.map
            ((g.op, 𝟙 ω) : ((Opposite.op K', ω) : _ × _) ⟶ (Opposite.op K, ω)))).hom := by
  have hmap := congrArg (fun φ => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map φ)
    (localDualityMor_naturality I hI f hf ω E θ g)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hmap
  have hx := congrArg (fun m => ModuleCat.Hom.hom m x) hmap
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hx
  have h1 : localDualityMatlisEquiv I hI f hf ω E θ n K' hiso'
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((localCohomologyEndofunctor A I hI).map g)).hom x) =
      homologyDerivedHomInjectiveEquiv
        ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K', ω)) E n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            (localDualityMor I hI f hf ω E θ K')).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            ((localCohomologyEndofunctor A I hI).map g)).hom x)) := rfl
  have h3 := homologyDerivedHomInjectiveEquiv_comp
    ((derivedHomAdjunction (R := A)).hom.map
      ((g.op, 𝟙 ω) : ((Opposite.op K', ω) : _ × _) ⟶ (Opposite.op K, ω))) E n
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (localDualityMor I hI f hf ω E θ K)).hom x)
  rw [h1, hx]
  exact h3

end Dualizing.LocalDuality

end
