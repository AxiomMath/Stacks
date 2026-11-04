module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison

/-!
# Maps out of a completion are maps into the inverse limit

Let `X` be a locally Noetherian scheme, `I` a quasi-coherent ideal sheaf on `X`, `G` a coherent
`𝒪_X`-module and `(F_n)` a coherent adic system along `I`. A morphism `G^∧ ⟶ (F_n)` in
`Coh(X, I)` is the same thing as a morphism `G ⟶ lim F_n` of `𝒪_X`-modules: the completion
functor of Stacks 0880 is, on morphisms out of a coherent module, left adjoint to taking the
inverse limit.

## Main definitions

* `Stacks.Algebraization.homToAdicSystem` — the map of coherent adic systems determined by a
  morphism into the inverse limit.
* `Stacks.Algebraization.adicSystemToHom` — the morphism into the inverse limit determined by a
  map of coherent adic systems.
* `Stacks.Algebraization.completionHomLimitEquiv` — **the adjunction**, as an isomorphism of
  abelian groups.

## Main results

* `Stacks.Algebraization.comp_eqToHom_symm_comp_eqToHom` — cancelling a mutually inverse pair of
  `eqToHom`s out of the middle of a composite, in an abstract category.
* `Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot` — a morphism whose target is
  annihilated by `I ^ n` kills the subsheaf `I ^ n` of its source.
* `Stacks.Algebraization.completionProjection_homToAdicSystem` and
  `Stacks.Algebraization.adicSystemToHom_π` — the composites of the two constructions with the
  projections of `G` onto the terms of its completion and with the limit projections.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! ### A morphism into a module annihilated by `I ^ n` kills `I ^ n` of its source -/

/-- If the subsheaf `I ^ n N` of `N` vanishes then `I(U) ^ n` annihilates the sections of `N`
over every affine open `U`. -/
public theorem idealPower_smul_sections_eq_bot_of_idealPowerMultiple_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (N : X.Modules) (hN : idealPowerMultiple I n N = ⊥)
    (U : X.affineOpens) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(N, U)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  have hgen := (idealPowerMultiple_le_iff I n N (idealPowerMultiple I n N)).mp le_rfl U
  rw [hN] at hgen
  exact hgen.trans (le_of_eq (SheafOfModules.Submodule.bot_obj N (op U.1)))

/-- A morphism whose target has vanishing `I ^ n`-multiple kills the subsheaf `I ^ n` of its
source, hence factors through the quotient by it. -/
public theorem comp_eq_zero_of_idealPowerMultiple_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N)
    (hN : idealPowerMultiple I n N = ⊥) :
    ((idealPowerMultiple I n M).ι :
        ((idealPowerMultiple I n M).toSheafOfModules : X.Modules) ⟶ M) ≫ f =
      (0 : ((idealPowerMultiple I n M).toSheafOfModules : X.Modules) ⟶ _) := by
  have hker := Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule I n f
    (idealPower_smul_sections_eq_bot_of_idealPowerMultiple_eq_bot I n N hN)
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  have hx := hker (op V) x.property
  rwa [kernelSubmodule_toSubmodule_obj] at hx

/-! ### The adjunction -/

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}

/-- The underlying sheaf of modules of a coherent module, with its presentation pinned to
`AlgebraicGeometry.Scheme.Modules`. -/
public abbrev coherentObj
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) : X.Modules := G.obj

/-- Cancelling a pair of mutually inverse `eqToHom`s out of the middle of a composite. -/
public theorem comp_eqToHom_symm_comp_eqToHom {C : Type*} [Category C] {A B B' D : C}
    (a : A ⟶ B') (h : B = B') (d : B' ⟶ D) :
    (a ≫ eqToHom h.symm) ≫ (eqToHom h ≫ d) = a ≫ d := by
  rw [Category.assoc, ← Category.assoc (eqToHom h.symm), eqToHom_trans, eqToHom_refl,
    Category.id_comp]

/-- The level-`n` component of the map of coherent adic systems determined by a morphism into the
inverse limit: the map out of the `n`-th term `G / I ^ (n+1) G` of `G^∧` induced by the composite
`G ⟶ lim F_n ⟶ F_n`. -/
public noncomputable def homToAdicSystemApp
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : coherentObj G ⟶ limit F.obj) (n : ℕᵒᵖ) :
    ((completionFunctor X I).obj G).obj.obj n ⟶ F.obj.obj n :=
  eqToHom (completionFunctor_obj X I G n.unop) ≫
    cokernel.desc (C := X.Modules) (idealPowerMultiple I (n.unop + 1) G.obj).ι
      (f ≫ limit.π F.obj n)
      (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n.unop + 1) _ (F.property.2.1 n.unop))

/-- Composing `homToAdicSystemApp` with the projection of `G` onto the `n`-th term of its
completion recovers the composite `G ⟶ lim F_n ⟶ F_n`. -/
public theorem completionProjection_homToAdicSystemApp
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : coherentObj G ⟶ limit F.obj) (n : ℕᵒᵖ) :
    completionProjection X I G n.unop ≫ homToAdicSystemApp G F f n =
      f ≫ limit.π F.obj n := by
  have hdesc := cokernel.π_desc (C := X.Modules) (idealPowerMultiple I (n.unop + 1) G.obj).ι
    (f ≫ limit.π F.obj n)
    (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n.unop + 1) _ (F.property.2.1 n.unop))
  rw [completionProjection, homToAdicSystemApp]
  exact (comp_eqToHom_symm_comp_eqToHom _ (completionFunctor_obj X I G n.unop) _).trans hdesc

/-- The map of coherent adic systems `G^∧ ⟶ (F_n)` determined by a morphism `G ⟶ lim F_n`. -/
public noncomputable def homToAdicSystem
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : coherentObj G ⟶ limit F.obj) :
    (completionFunctor X I).obj G ⟶ F :=
  ObjectProperty.homMk
    { app n := homToAdicSystemApp G F f n
      naturality := fun _m n a => by
        have hepi := epi_completionProjection X I G _m.unop
        have hL : completionProjection X I G _m.unop ≫
            (((completionFunctor X I).obj G).obj.map a ≫ homToAdicSystemApp G F f n) =
            f ≫ limit.π F.obj n :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ homToAdicSystemApp G F f n)
                (completionProjection_map X I G a)).trans
              (completionProjection_homToAdicSystemApp G F f n))
        have hR : completionProjection X I G _m.unop ≫
            (homToAdicSystemApp G F f _m ≫ F.obj.map a) = f ≫ limit.π F.obj n :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ F.obj.map a)
                (completionProjection_homToAdicSystemApp G F f _m)).trans
              ((Category.assoc _ _ _).trans (congrArg (fun k => f ≫ k) (limit.w F.obj a))))
        exact (cancel_epi _).mp (hL.trans hR.symm) }

/-- Composing the `n`-th component of `homToAdicSystem` with the projection of `G` onto the
`n`-th term of its completion recovers the composite `G ⟶ lim F_n ⟶ F_n`. -/
public theorem completionProjection_homToAdicSystem
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : coherentObj G ⟶ limit F.obj) (n : ℕᵒᵖ) :
    completionProjection X I G n.unop ≫ (homToAdicSystem G F f).hom.app n =
      f ≫ limit.π F.obj n :=
  completionProjection_homToAdicSystemApp G F f n

/-- The morphism `G ⟶ lim F_n` determined by a map of coherent adic systems `G^∧ ⟶ (F_n)`:
postcomposing the projections of `G` onto the terms of its completion with the map gives a cone
on `(F_n)` with vertex `G`. -/
public noncomputable def adicSystemToHom
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : (completionFunctor X I).obj G ⟶ F) : coherentObj G ⟶ limit F.obj :=
  limit.lift (C := X.Modules) F.obj ((Cone.postcompose f.hom).obj (completionCone X I G))

/-- The composite of `adicSystemToHom` with the `n`-th limit projection is the `n`-th component of
the given map of systems, precomposed with the projection of `G`. -/
public theorem adicSystemToHom_π
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (f : (completionFunctor X I).obj G ⟶ F) (n : ℕᵒᵖ) :
    adicSystemToHom G F f ≫ limit.π F.obj n =
      completionProjection X I G n.unop ≫ f.hom.app n :=
  limit.lift_π (F := F.obj) ((Cone.postcompose f.hom).obj (completionCone X I G)) n

/-- **Maps out of a completion are maps into the inverse limit.** For a coherent module `G` and a
coherent adic system `(F_n)` along `I` on a locally Noetherian scheme, the morphisms
`G^∧ ⟶ (F_n)` in `Coh(X, I)` are the morphisms `G ⟶ lim F_n` of `𝒪_X`-modules. -/
public noncomputable def completionHomLimitEquiv
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I) :
    (coherentObj G ⟶ limit F.obj) ≃+ ((completionFunctor X I).obj G ⟶ F) where
  toFun := homToAdicSystem G F
  invFun := adicSystemToHom G F
  left_inv f :=
    limit.hom_ext fun n =>
      (adicSystemToHom_π G F (homToAdicSystem G F f) n).trans
        (completionProjection_homToAdicSystem G F f n)
  right_inv f := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have hepi := epi_completionProjection X I G n.unop
    exact (cancel_epi _).mp
      ((completionProjection_homToAdicSystem G F (adicSystemToHom G F f) n).trans
        (adicSystemToHom_π G F f n))
  map_add' f g := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have hepi := epi_completionProjection X I G n.unop
    refine (@cancel_epi _ _ _ _ _ (completionProjection X I G n.unop) hepi _ _).mp ?_
    rw [completionProjection_homToAdicSystem, Preadditive.add_comp]
    change _ = completionProjection X I G n.unop ≫
      ((homToAdicSystem G F f).hom.app n + (homToAdicSystem G F g).hom.app n)
    rw [← completionProjection_homToAdicSystem G F f n,
      ← completionProjection_homToAdicSystem G F g n]
    exact (Preadditive.comp_add _ _ _ _ _ _).symm

end Stacks.Algebraization

end
