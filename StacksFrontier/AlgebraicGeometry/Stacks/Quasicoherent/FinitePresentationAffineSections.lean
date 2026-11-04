module

public import StacksFrontier.Algebra.Module.FinitePresentation.PiDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineMemberBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleFinitePresentation

/-!
# Sections over affine objects of a module of finite presentation

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be an `𝒪_𝒳`-module of
finite presentation on the associated fppf site (Modules on Sites, Definition 03DL (7)).  This
file proves that over every object `y` of `𝒳` lying over an affine scheme the sections `F(y)` form
a module of finite presentation over the ring `Γ(y)` of global functions.

The proof has two steps.

* *Over a presented slice.*  If the restriction of a module to the slice at an object `x` has a
  finite global presentation, its sections over an affine object `W` of that slice are the
  cokernel of the map of sections of the presentation: the presenting morphism is surjective on
  the sections over `W` and its kernel there is the image of the relations
  (`AlgebraicGeometry.FibredSite.surjective_val_app_of_isColimit_of_isAffineOver`,
  `AlgebraicGeometry.FibredSite.mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver`),
  and the sections of the two finite coproducts of copies of the structure sheaf over `W` are
  finite free (`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs`).
* *Descent.*  Finite presentation of `F` supplies a covering sieve of `y` on whose members `F` has
  a finite global presentation; it contains a finite family of affine objects `zⱼ ⟶ y` which is
  fppf in schemes (`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le`), so that
  `∏ Γ(zⱼ)` is faithfully flat over `Γ(y)`.  A quasi-coherent module is cartesian between affine
  objects (`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_eq_restriction`), so
  `F(zⱼ) = Γ(zⱼ) ⊗_{Γ(y)} F(y)`, each `F(zⱼ)` is of finite presentation by the first step, and
  `Module.FinitePresentation.of_forall_bijective_liftBaseChange_pi` descends.

## Main results

* `AlgebraicGeometry.FibredSite.finitePresentation_sections_of_hasFiniteGlobalPresentation`: the
  first step.
* `AlgebraicGeometry.FibredSite.finitePresentation_obj_of_isFinitePresentationOnSite`: the
  sections of a module of finite presentation over an affine object are of finite presentation.
* `AlgebraicGeometry.FibredSite.isFinitePresentationOnSite_restrictSiteModules_etale_of_fppf`: a
  module of finite presentation on the fppf site of an algebraic stack is of finite presentation
  on its étale site.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

/-- A module that is the cokernel of a linear map from a finite module to a finite free module
is of finite presentation. -/
private theorem finitePresentation_of_ker_eq_range {A Q P N ι κ : Type*} [CommRing A]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    [Finite ι] [Finite κ] (bP : Module.Basis ι A P) (bQ : Module.Basis κ A Q) (a : Q →ₗ[A] P)
    (b : P →ₗ[A] N) (hb : Function.Surjective b) (hab : LinearMap.ker b = LinearMap.range a) :
    Module.FinitePresentation A N :=
  have := Module.Free.of_basis bP
  have := Module.Finite.of_basis bP
  have := Module.Finite.of_basis bQ
  Module.finitePresentation_of_free_of_surjective b hb <| by
    rw [hab, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map a

include hp in
/-- **The sections of a finitely presented module over an affine object of a slice are of finite
presentation.**  Let `M` be a sheaf of modules on the slice at `x` with a finite global
presentation, and let `W` be an object of the slice lying over an affine scheme.  Then `M(W)` is a
module of finite presentation over any commutative ring identified with the ring of sections of
the structure sheaf at `W`, acting compatibly: it is the cokernel of the map between the finite
free modules of sections of the presentation. -/
theorem finitePresentation_sections_of_hasFiniteGlobalPresentation
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hM : M.HasFiniteGlobalPresentation) (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left))
    (A : Type*) [CommRing A] [Module A (M.val.obj (op W))]
    (fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u) ≃+* A)
    (hfA : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (n : M.val.obj (op W)), fA c • n = c • n) :
    Module.FinitePresentation A (M.val.obj (op W)) := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := hM
  have _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      AddCommGrpCat.{max v w u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max v w u, w, max v w} _
  have _ : ((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max v w u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max v w u, max v w, w} _
  have _ : Epi b := Cofork.IsColimit.epi hcok
  have hab' : a.val ≫ b.val = 0 := by rw [← SheafOfModules.comp_val, hab]; rfl
  let NU := SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M
  let mQ : Module A (Q.val.obj (op W)) := Module.compHom _ fA.symm.toRingHom
  let mP : Module A (P.val.obj (op W)) := Module.compHom _ fA.symm.toRingHom
  let mN : Module A (NU.val.obj (op W)) := Module.compHom _ fA.symm.toRingHom
  have hfQ : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (q : Q.val.obj (op W)), fA c • q = c • q := fun c q =>
    congrArg (fun d : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u)
      => d • q) (fA.symm_apply_apply c)
  have hfP : ∀ (c : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u))
      (q : P.val.obj (op W)), fA c • q = c • q := fun c q =>
    congrArg (fun d : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W) : Type u)
      => d • q) (fA.symm_apply_apply c)
  let aW : Q.val.obj (op W) →ₗ[A] P.val.obj (op W) :=
    { toFun := fun q => a.val.app (op W) q
      map_add' := map_add (a.val.app (op W)).hom
      map_smul' := fun c q => (a.val.app (op W)).hom.map_smul (fA.symm c) q }
  let bW : P.val.obj (op W) →ₗ[A] NU.val.obj (op W) :=
    { toFun := fun q => b.val.app (op W) q
      map_add' := map_add (b.val.app (op W)).hom
      map_smul' := fun c q => (b.val.app (op W)).hom.map_smul (fA.symm c) q }
  have hNU : Module.FinitePresentation A (NU.val.obj (op W)) := by
    refine finitePresentation_of_ker_eq_range
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι hP W hW fA hfP)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp κ hQ W hW fA hfQ) aW bW
      (surjective_val_app_of_isColimit_of_isAffineOver B S hS p hp κ ι hQ hP a b hab' hab hcok W hW)
      (le_antisymm (fun z hz => ?_) ?_)
    · exact mem_range_val_app_of_isColimit_cokernelCofork_of_isAffineOver B S hS p hp
        κ ι hQ hP a b hab hab' hcok W hW (z := z) hz
    · rintro _ ⟨q, rfl⟩
      have hz := congr($(hab).val.app (op W) q)
      rwa [SheafOfModules.comp_val] at hz
  have hA' : ∀ (c : A) (m : M.val.obj (op W)), c • m = fA.symm c • m := fun c m => by
    rw [← hfA (fA.symm c) m, fA.apply_symm_apply]
  let e : NU.val.obj (op W) ≃ₗ[A] M.val.obj (op W) :=
    { toFun := fun m => ULift.down m
      map_add' := fun _ _ => rfl
      map_smul' := fun c m => (hA' c m.down).symm
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.FinitePresentation.of_equiv e

include hp in
/-- **The sections of a module over an affine object lying over a presented object are of finite
presentation.**  If the restriction of `F` to the slice at `V` has a finite global presentation and
`g : z ⟶ V` is an arrow out of an object lying over an affine scheme, then `F(z)` is of finite
presentation over `Γ(z)`.  This is
`AlgebraicGeometry.FibredSite.finitePresentation_sections_of_hasFiniteGlobalPresentation` at the
object `Over.mk g` of the slice, whose sections are those of `F` over `z`. -/
theorem finitePresentation_obj_of_hasFiniteGlobalPresentation_over
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) {V z : 𝒳} (g : z ⟶ V)
    (hV : (F.over V).HasFiniteGlobalPresentation) (hz : IsAffineOver B S hS (p.obj z)) :
    letI := objModule B S hS p hp F z
    Module.FinitePresentation (objRing B S hS p z) (F.val.obj (op z)) :=
  let : Module (objRing B S hS p z) ((F.over V).val.obj (op (Over.mk g))) :=
    objModule B S hS p hp F z
  finitePresentation_sections_of_hasFiniteGlobalPresentation B S hS p hp (F.over V) hV
    (Over.mk g) hz (objRing B S hS p z) (RingEquiv.refl _) fun _ _ => rfl

include hp in
/-- **The sections of a quasi-coherent module of finite presentation over an affine object are of
finite presentation** over the ring of global functions.

Finite presentation supplies a covering sieve of `y` on whose generators the module has a finite
global presentation; the sieve contains a finite family of affine objects `zⱼ ⟶ y` which is fppf
in schemes, so `∏ Γ(zⱼ)` is faithfully flat over `Γ(y)`; the sections over each `zⱼ` are of
finite presentation by
`AlgebraicGeometry.FibredSite.finitePresentation_obj_of_hasFiniteGlobalPresentation_over` and are
the base change of the sections over `y` because a quasi-coherent module is cartesian between
affine objects; and finite presentation descends along the product
(`Module.FinitePresentation.of_forall_bijective_liftBaseChange_pi`). -/
theorem finitePresentation_objRing_of_isFinitePresentationOnSite
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) (hfp : F.IsFinitePresentationOnSite) (y : 𝒳)
    (hy : IsAffineOver B S hS (p.obj y)) :
    letI := objModule B S hS p hp F y
    Module.FinitePresentation (objRing B S hS p y) (F.val.obj (op y)) := by
  let := objModule B S hS p hp F y
  obtain ⟨I, V, f, hcov, hV⟩ := hfp.locally_hasFiniteGlobalPresentation y
  obtain ⟨n, z, φ, hzaff, hmem, -, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le B S hS p hp hy hcov
  let : ∀ i, Algebra (objRing B S hS p y) (objRing B S hS p (z i)) := fun i =>
    objAlgebra B S hS p (φ i)
  let : ∀ i, Module (objRing B S hS p (z i)) (F.val.obj (op (z i))) := fun i =>
    objModule B S hS p hp F (z i)
  let : ∀ i, Module (objRing B S hS p y) (F.val.obj (op (z i))) := fun i =>
    Module.compHom _ (algebraMap (objRing B S hS p y) (objRing B S hS p (z i)))
  have : ∀ i, IsScalarTower (objRing B S hS p y) (objRing B S hS p (z i))
      (F.val.obj (op (z i))) := fun i => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) := hy
  have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := hzaff
  have : Module.FaithfullyFlat (objRing B S hS p y) (∀ i, objRing B S hS p (z i)) :=
    _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
      (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) hfppf fun _ => rfl
  have : ∀ i, Module.FinitePresentation (objRing B S hS p (z i)) (F.val.obj (op (z i))) := by
    intro i
    obtain ⟨j, g, -⟩ := (Sieve.mem_ofArrows_iff V f (φ i)).1 (hmem i)
    exact finitePresentation_obj_of_hasFiniteGlobalPresentation_over B S hS p hp F g (hV j)
      (hzaff i)
  exact Module.FinitePresentation.of_forall_bijective_liftBaseChange_pi
    (fun i => objRing B S hS p (z i)) (objRing B S hS p y) (F.val.obj (op y))
    (fun i => F.val.obj (op (z i))) (fun i => restrictionLinear F (φ i))
    (fun i => bijective_liftBaseChange_of_eq_restriction F hF (φ i) hy (hzaff i) _ fun _ => rfl)

include hp in
/-- **The sections of a module of finite presentation over an object lying over an affine scheme
are of finite presentation** over the ring of sections of the structure sheaf there.  A module of
finite presentation is quasi-coherent, so this is
`AlgebraicGeometry.FibredSite.finitePresentation_objRing_of_isFinitePresentationOnSite`. -/
theorem finitePresentation_obj_of_isFinitePresentationOnSite
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    [F.IsFinitePresentationOnSite] (y : 𝒳)
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y))) :
    Module.FinitePresentation ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op y))
      (F.val.obj (op y)) :=
  finitePresentation_objRing_of_isFinitePresentationOnSite B S hS p hp F inferInstance
    inferInstance y hy

/-- **A module of finite presentation on the fppf site of an algebraic stack is of finite
presentation on its étale site.**  Its sections over affine objects are of finite presentation
(`AlgebraicGeometry.FibredSite.finitePresentation_obj_of_isFinitePresentationOnSite`), and a
quasi-coherent module with that property is of finite presentation on the étale site
(`AlgebraicGeometry.FibredSite.isFinitePresentationOnSite_restrictSiteModules_etale`).  This is the
finiteness hypothesis on the étale side which Stacks 06WM (5) and Stacks 0771 (7) consume. -/
theorem isFinitePresentationOnSite_restrictSiteModules_etale_of_fppf
    (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) (F : Stack.fppfModules B S hS 𝒴)
    [F.IsFinitePresentationOnSite] :
    (restrictSiteModules B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .etale
      F).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_restrictSiteModules_etale B S hS 𝒴 F inferInstance
    (finitePresentation_obj_of_isFinitePresentationOnSite B S hS _ _ F)

end AlgebraicGeometry.FibredSite
