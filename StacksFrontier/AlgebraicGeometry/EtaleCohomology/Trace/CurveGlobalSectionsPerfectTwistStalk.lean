module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTorAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectStalks

/-!
# Stalks of the twists of a sheaf of modules

Let `Y` be a scheme, `Λ` a ring, not necessarily commutative, and `Φ` a point of the small étale
site of `Y`. For a finite free right `Λ`-module `N` and a sheaf `G` of left `Λ`-modules, the stalk
of the twist `N ⊗[Λ] G` at `Φ` is `N ⊗[Λ] G_Φ`, naturally in `N` and `G`: tensoring with `N` is a
finite power, which is its own adjoint and so commutes with the colimit defining the stalk. This
is how the proof of [Stacks, Tag 03TV] checks the exactness of the twist complex on stalks.

## Main definitions

* `Stacks.SheafTwist.powModuleAdj`: the finite power functor is its own right adjoint.
* `Stacks.SheafTwist.twistFiberIso`: the stalk of `N ⊗[Λ] G` is `N ⊗[Λ] G_Φ`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ]

section Pow

variable (ι : Type (max (u + 1) r)) [Fintype ι] [DecidableEq ι]

/-- **A finite power of left modules is its own right adjoint**: a linear map out of `ι → M` is
the family of its restrictions to the coordinates, and so is a linear map into `ι → N`. -/
def powModuleAdj : powModule.{u, r} (Λ := Λ) ι ⊣ powModule.{u, r} (Λ := Λ) ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f => ModuleCat.ofHom (LinearMap.pi fun i =>
            (f.hom : (ι → M) →ₗ[Λ] N) ∘ₗ LinearMap.single Λ (fun _ : ι => (M : Type _)) i)
          invFun := fun g => ModuleCat.ofHom (∑ i, LinearMap.proj i ∘ₗ
            (g.hom : M →ₗ[Λ] (ι → N)) ∘ₗ LinearMap.proj (R := Λ) (φ := fun _ : ι => (M : Type _)) i)
          left_inv := fun f => by
            refine ModuleCat.hom_ext (LinearMap.ext fun (x : ι → M) => ?_)
            let f' : (ι → M) →ₗ[Λ] N := f.hom
            change (∑ i, LinearMap.proj i ∘ₗ (LinearMap.pi fun i =>
              f' ∘ₗ LinearMap.single Λ (fun _ : ι => (M : Type _)) i) ∘ₗ
                LinearMap.proj (R := Λ) (φ := fun _ : ι => (M : Type _)) i) x = f' x
            rw [LinearMap.sum_apply]
            change ∑ i, f' (Pi.single i (x i)) = f' x
            rw [← map_sum, Finset.univ_sum_single]
          right_inv := fun g => by
            refine ModuleCat.hom_ext (LinearMap.ext fun m => funext fun i => ?_)
            let g' : M →ₗ[Λ] (ι → N) := g.hom
            change (∑ j, LinearMap.proj j ∘ₗ g' ∘ₗ
              LinearMap.proj (R := Λ) (φ := fun _ : ι => (M : Type _)) j) (Pi.single i m) = g' m i
            rw [LinearMap.sum_apply]
            change ∑ j, g' (Pi.single (M := fun _ : ι => (M : Type _)) i m j) j = g' m i
            rw [Finset.sum_eq_single i (fun j _ hj => by
              rw [Pi.single_eq_of_ne hj, map_zero]
              rfl) (by simp), Pi.single_eq_same] }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun (x : ι → X') => ?_)
        let g' : X →ₗ[Λ] (ι → Y) := g.hom
        let f' : X' →ₗ[Λ] X := f.hom
        change (∑ i, LinearMap.proj i ∘ₗ (g' ∘ₗ f') ∘ₗ
            LinearMap.proj (R := Λ) (φ := fun _ : ι => (X' : Type _)) i) x =
          (∑ i, LinearMap.proj i ∘ₗ g' ∘ₗ
            LinearMap.proj (R := Λ) (φ := fun _ : ι => (X : Type _)) i) (fun i => f' (x i))
        rw [LinearMap.sum_apply, LinearMap.sum_apply]
        rfl
      homEquiv_naturality_right := fun f g => ModuleCat.hom_ext (LinearMap.ext fun m => rfl) }

end Pow

section Fiber

variable (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)

/-- **Tensoring with a finite free right module preserves colimits**: it is a finite power of
left modules followed by the forgetful functor to abelian groups, both of them left adjoints. -/
theorem preservesColimitsOfSize_tensorAb (N : FiniteFree.{max (u + 1) r} Λ) :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorAb D N.obj) := by
  classical
  let b := Module.Free.chooseBasis (MulOpposite Λ) N.obj
  have : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (powModule.{u, r} (Λ := Λ) (Module.Free.ChooseBasisIndex (MulOpposite Λ) N.obj)) :=
    (powModuleAdj _).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (Stacks.EtaleResolution.forgetAb.{u + 1} Λ) :=
    (Stacks.EtaleResolution.forgetCoextendAdj.{u + 1} Λ).leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso (tensorAbIso.{u, r} _ D b).symm

variable (Y : Scheme.{u}) (Φ : GrothendieckTopology.Point.{max (u + 1) r} Y.smallEtaleTopology)

/-- **The stalk of a twist is the twist of the stalk**: `(N ⊗[Λ] G)_Φ ≅ N ⊗[Λ] G_Φ`. -/
def twistFiberIso (N : FiniteFree.{max (u + 1) r} Λ)
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    Φ.sheafFiber.obj (((twist.{u, r} D Y).obj N).obj G) ≅
      (tensorAb D N.obj).obj (Φ.sheafFiber.obj G) :=
  have := preservesColimitsOfSize_tensorAb.{u, r} D N
  (Φ.sheafFiberCompIso (tensorAb D N.obj)).app G

/-- The identification of the stalk of a twist is natural in the sheaf. -/
@[reassoc]
lemma twistFiberIso_hom_naturality_right (N : FiniteFree.{max (u + 1) r} Λ)
    {G G' : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y} (g : G ⟶ G') :
    Φ.sheafFiber.map (((twist.{u, r} D Y).obj N).map g) ≫ (twistFiberIso.{u, r} D Y Φ N G').hom =
      (twistFiberIso.{u, r} D Y Φ N G).hom ≫ (tensorAb D N.obj).map (Φ.sheafFiber.map g) :=
  have := preservesColimitsOfSize_tensorAb.{u, r} D N
  (Φ.sheafFiberCompIso (tensorAb D N.obj)).hom.naturality g

/-- The identification of the stalk of a twist is natural in the finite free module. -/
@[reassoc]
lemma twistFiberIso_hom_naturality_left {N N' : FiniteFree.{max (u + 1) r} Λ} (f : N ⟶ N')
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    Φ.sheafFiber.map (((twist.{u, r} D Y).map f).app G) ≫ (twistFiberIso.{u, r} D Y Φ N' G).hom =
      (twistFiberIso.{u, r} D Y Φ N G).hom ≫
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          ((D.ordinary.map f.hom).app (Φ.sheafFiber.obj G)) := by
  have := preservesColimitsOfSize_tensorAb.{u, r} D N
  have := preservesColimitsOfSize_tensorAb.{u, r} D N'
  apply Φ.presheafFiber_hom_ext
  intro X x
  have h₁ := Φ.toPresheafFiber_presheafFiberCompIso_hom_app (tensorAb D N.obj) X x G.obj
  have h₂ := Φ.toPresheafFiber_presheafFiberCompIso_hom_app (tensorAb D N'.obj) X x G.obj
  show Φ.toPresheafFiber X x (G.obj ⋙ tensorAb D N.obj) ≫
      Φ.presheafFiber.map (Functor.whiskerLeft G.obj
        (Functor.whiskerRight (D.ordinary.map f.hom) (forget₂ (ModuleCat ℤ) AddCommGrpCat))) ≫
        (Φ.presheafFiberCompIso (tensorAb D N'.obj)).hom.app G.obj ≫ 𝟙 _ =
    Φ.toPresheafFiber X x (G.obj ⋙ tensorAb D N.obj) ≫
      ((Φ.presheafFiberCompIso (tensorAb D N.obj)).hom.app G.obj ≫ 𝟙 _) ≫
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          ((D.ordinary.map f.hom).app (Φ.presheafFiber.obj G.obj))
  rw [Category.comp_id, Category.comp_id, Φ.toPresheafFiber_naturality_assoc, h₂,
    ← Category.assoc, h₁]
  exact ((Functor.whiskerRight (D.ordinary.map f.hom)
    (forget₂ (ModuleCat ℤ) AddCommGrpCat)).naturality (Φ.toPresheafFiber X x G.obj)).symm

/-- **The stalk of the twist bicomplex is the bicomplex of twisted stalks**: termwise
`(R^p ⊗[Λ] I^q)_Φ ≅ R^p ⊗[Λ] I^q_Φ`, compatibly with both differentials. -/
def twistFiberBicomplexIso (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) :
    HomologicalComplex₂.TotalMap.mapBicomplex Φ.sheafFiber
        (((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj R |>.obj I) ≅
      HomologicalComplex₂.TotalMap.mapBicomplex
        (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r})
        ((((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙
          D.ordinary).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj R).obj ((Φ.sheafFiber.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => twistFiberIso.{u, r} D Y Φ (R.X p) (I.X q))
      (fun q q' _ => (twistFiberIso_hom_naturality_right.{u, r} D Y Φ (R.X p) (I.d q q')).symm))
    (fun p p' _ => by
      ext q : 1
      exact (twistFiberIso_hom_naturality_left.{u, r} D Y Φ (R.d p p') (I.X q)).symm)

end Fiber

/-! ### Tensoring with a finite projective module is exact -/

section Projective

variable (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)

/-- **Tensoring with a finite projective left module preserves homology**: such a module is a
retract of a finite free one, tensoring with which preserves homology, and a retract of an exact
sequence of abelian groups is exact. -/
lemma preservesHomology_ordinary_flip_obj_of_projective (M : ModuleCat.{max (u + 1) r} Λ)
    [Module.Finite Λ M] [Module.Projective Λ M] : (D.ordinary.flip.obj M).PreservesHomology := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ M
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let L := ModuleCat.of Λ (ULift.{max (u + 1) r} (Fin n → Λ))
  let s : M ⟶ L := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ σ)
  let t : L ⟶ M := ModuleCat.ofHom (π ∘ₗ ULift.moduleEquiv.toLinearMap)
  have hst : s ≫ t = 𝟙 M := by
    ext m
    exact LinearMap.congr_fun hσ m
  have := preservesHomology_ordinary_flip_obj_of_free D L
  refine ((Functor.exact_tfae (D.ordinary.flip.obj M)).out 2 3).1 fun S hS => ?_
  have hSL := hS.map (D.ordinary.flip.obj L)
  rw [ShortComplex.moduleCat_exact_iff] at hSL ⊢
  intro x hx
  have hx' : (S.map (D.ordinary.flip.obj L)).g (((D.ordinary.obj S.X₂).map s).hom x) = 0 := by
    show ((D.ordinary.obj S.X₂).map s ≫ (D.ordinary.map S.g).app L).hom x = 0
    rw [(D.ordinary.map S.g).naturality s]
    show ((D.ordinary.obj S.X₃).map s).hom ((S.map (D.ordinary.flip.obj M)).g x) = 0
    rw [hx, map_zero]
  obtain ⟨y, hy⟩ := hSL _ hx'
  refine ⟨((D.ordinary.obj S.X₁).map t).hom y, ?_⟩
  show (((D.ordinary.obj S.X₁).map t ≫ (D.ordinary.map S.f).app M)).hom y = x
  rw [(D.ordinary.map S.f).naturality t]
  show ((D.ordinary.obj S.X₂).map t).hom ((S.map (D.ordinary.flip.obj L)).f y) = x
  rw [hy]
  show ((D.ordinary.obj S.X₂).map s ≫ (D.ordinary.obj S.X₂).map t).hom x = x
  rw [← Functor.map_comp, hst, CategoryTheory.Functor.map_id]
  rfl

end Projective

end Stacks.SheafTwist

end
