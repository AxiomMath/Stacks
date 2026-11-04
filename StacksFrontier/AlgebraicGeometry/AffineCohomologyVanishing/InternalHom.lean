module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFree
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyOfAProduct
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback

/-!
# The first cohomology of an internal hom out of a locally projective module on an affine scheme

A quasi-coherent module on an affine scheme is the sheaf associated to its module of global
sections, and that module is projective exactly when the sheaf is locally projective. A
projective module is a retract of a free module, so a locally projective quasi-coherent module
on an affine scheme is a retract of a free sheaf of modules.

That is the geometric input to the vanishing of the first cohomology of the internal hom out of
a locally projective module. Precomposition makes the internal hom contravariant in its source,
so it carries that retract to a retract of the internal hom out of the free module, which is a
product of copies of the target; the first cohomology of a product of quasi-coherent modules on
an affine scheme vanishes, and cohomology in a fixed degree is a functor, so vanishing passes to
a retract.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_retract_free_of_isLocallyProjective`: a locally
  projective quasi-coherent module on an affine scheme is a retract of a free module.
* `AlgebraicGeometry.Scheme.Modules.isLocallyProjective_of_iso`: being locally projective is
  invariant under isomorphism.
* `Stacks.Cohomology.Affine.isZero_cohomology_of_retract`: vanishing of cohomology in a fixed
  degree passes to a retract.
* `Stacks.Cohomology.Affine.isZero_firstCohomology_sheafHom_of_isLocallyProjective`: the first
  cohomology of the internal hom from a locally projective quasi-coherent module to a
  quasi-coherent module on an affine scheme vanishes.

## Implementation notes

The reduction to `Spec` of the ring of global sections is along `AlgebraicGeometry.Scheme.isoSpec`
and the restriction functor on sheaves of modules, rather than along the pullback functor: the
restriction functor along an isomorphism has an explicit inverse, which is what carries a retract
back. The two are identified by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`,
which is where the pullback statement for local projectivity is applied.

Over `Spec R` the sections over the whole space are a module over `Γ(Spec R, ⊤)` rather than over
`R` itself. That comparison is not redone here: it is the content of
`AlgebraicGeometry.isLocallyProjective_tilde_iff_projective`, which is applied to the sheaf
associated to the module of global sections.

## References

* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
* [Stacks Project, Tag 05JQ](https://stacks.math.columbia.edu/tag/05JQ)
* [Stacks Project, Tag 060M](https://stacks.math.columbia.edu/tag/060M)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0D0A](https://stacks.math.columbia.edu/tag/0D0A)
* [Stacks Project, Tag 0D0E](https://stacks.math.columbia.edu/tag/0D0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Being locally projective is invariant under isomorphism of sheaves of modules: an
isomorphism is a bijection on the sections over every open, linearly over the functions on
that open. -/
theorem isLocallyProjective_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : IsLocallyProjective M) : IsLocallyProjective N := by
  intro U hU
  let : Module Γ(X, U) Γ(N, U) := (N.val.obj (.op U)).isModule
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := fun x => e.hom.app U x
      map_add' := fun x y => map_add (e.hom.app U).hom x y
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul e.hom r x }
  exact @Module.Projective.of_equiv' Γ(X, U) _ Γ(N, U) _ (N.val.obj (.op U)).isModule
    Γ(M, U) _ (M.val.obj (.op U)).isModule (hM U hU)
    (LinearEquiv.ofBijective φ (ConcreteCategory.bijective_of_isIso (e.hom.app U)))

/-- The sheaf associated to a projective module is a retract of a free sheaf of modules: a
projective module is a retract of a free module, and the construction `M ↦ M~` carries that
retract over, taking a free module to a free sheaf. -/
private theorem exists_retract_free_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.Projective R M] :
    ∃ I : Type u, Nonempty (Retract (tilde M) (SheafOfModules.free I)) := by
  classical
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R M).out
  let s : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  let eF : tilde (ModuleCat.of R (M →₀ R)) ≅ SheafOfModules.free M := tildeFinsupp M
  have hjr : (tilde.map (ModuleCat.ofHom i) ≫ eF.hom) ≫
      (eF.inv ≫ tilde.map (ModuleCat.ofHom s)) = 𝟙 (tilde M) := by
    calc
      _ = tilde.map (ModuleCat.ofHom i) ≫ (eF.hom ≫ eF.inv) ≫
            tilde.map (ModuleCat.ofHom s) := by cat_disch
      _ = tilde.map (ModuleCat.ofHom i) ≫ tilde.map (ModuleCat.ofHom s) := by
        rw [eF.hom_inv_id, Category.id_comp]
      _ = tilde.map (ModuleCat.ofHom (s.comp i)) := by
        rw [← tilde.map_comp, ModuleCat.ofHom_comp]
      _ = 𝟙 (tilde M) := by
        rw [show s.comp i = LinearMap.id from LinearMap.ext hi]
        exact tilde.map_id
  exact ⟨M, ⟨⟨_, _, hjr⟩⟩⟩

/-- A locally projective quasi-coherent module on `Spec R` is a retract of a free module: it is
the sheaf associated to its module of global sections, that module is projective, and the sheaf
associated to a projective module is a retract of a free sheaf. -/
private theorem exists_retract_free_spec (R : CommRingCat.{u}) (F : (Spec R).Modules)
    [F.IsQuasicoherent] (hF : IsLocallyProjective F) :
    ∃ I : Type u, Nonempty (Retract F (SheafOfModules.free I)) := by
  let e : F ≅ tilde (moduleSpecΓFunctor.obj F) := (asIso F.fromTildeΓ).symm
  have : Module.Projective R (moduleSpecΓFunctor.obj F) :=
    (isLocallyProjective_tilde_iff_projective R (moduleSpecΓFunctor.obj F)).mp
      (isLocallyProjective_of_iso e hF)
  obtain ⟨I, ⟨r⟩⟩ := exists_retract_free_tilde R (moduleSpecΓFunctor.obj F)
  exact ⟨I, ⟨(Retract.ofIso e).trans r⟩⟩

/-- **A locally projective quasi-coherent module on an affine scheme is a retract of a free
sheaf of modules.** -/
theorem exists_retract_free_of_isLocallyProjective (T : Scheme.{u}) [IsAffine T] (F : T.Modules)
    [F.IsQuasicoherent] (hF : IsLocallyProjective F) :
    ∃ I : Type u, Nonempty (Retract F (SheafOfModules.free I)) := by
  let e := T.isoSpec
  let N := F.restrict e.inv
  obtain ⟨I, ⟨rN⟩⟩ := exists_retract_free_spec Γ(T, ⊤) N
    (isLocallyProjective_of_iso ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app F).symm
      (pullback_isLocallyProjective e.inv F hF))
  let Q := Scheme.Modules.restrictFunctor e.hom
  let eFree : Q.obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ Q I
      (Adjunction.ofIsLeftAdjoint Q).leftAdjoint_preservesColimits.preservesColimitsOfShape
      (Scheme.Modules.restrictUnitIso e.hom).symm).symm
  let eF : F ≅ Q.obj N :=
    (((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId).app F).symm
  exact ⟨I, ⟨(Retract.ofIso eF).trans ((rN.map Q).trans (Retract.ofIso eFree))⟩⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Cohomology.Affine

/-- **Vanishing of cohomology passes to a retract.** Cohomology in a fixed degree is a functor,
so a retract of sheaves of modules becomes a retract of cohomology groups, and a retract of a
zero object is zero. -/
theorem isZero_cohomology_of_retract {X : Scheme.{u}} (F G : X.Modules) (n : ℕ)
    (i : F ⟶ G) (p : G ⟶ F) (hip : i ≫ p = 𝟙 F)
    (hG : IsZero (Hgroup X.ringCatSheaf ⊤ n G)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ n F) := by
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have h : (Hfunctor X.ringCatSheaf ⊤ n).map i ≫ (Hfunctor X.ringCatSheaf ⊤ n).map p = 𝟙 _ :=
    ((Functor.map_comp _ i p).symm.trans (congrArg _ hip)).trans
      ((Hfunctor X.ringCatSheaf ⊤ n).map_id F)
  rw [← h]
  simp only [hG.eq_zero_of_tgt ((Hfunctor X.ringCatSheaf ⊤ n).map i), zero_comp]

/-- **The first cohomology of an internal hom out of a locally projective module on an affine
scheme vanishes.** The source is a retract of a free module, so the internal hom is a retract of
the internal hom out of that free module, which is a product of copies of the target; the first
cohomology of that product vanishes because the first cohomology of a quasi-coherent module on
an affine scheme does. -/
@[stacks 0D0E]
theorem isZero_firstCohomology_sheafHom_of_isLocallyProjective (T : Scheme.{u}) [IsAffine T]
    (F G : T.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (H : SheafHom T.sheaf F G)
    (hF : Scheme.Modules.IsLocallyProjective F) :
    IsZero (Hgroup T.ringCatSheaf ⊤ 1 H.obj) := by
  obtain ⟨I, ⟨r⟩⟩ := Scheme.Modules.exists_retract_free_of_isLocallyProjective T F hF
  let Hfree := Stacks.SheafOfModules.sheafHomFree T.sheaf G I
  have hfree : IsZero (Hgroup T.ringCatSheaf ⊤ 1 Hfree.obj) :=
    Stacks.Cohomology.ModuleComparison.isZero_hgroup_pi_one T.ringCatSheaf ⊤
      (fun _ : I => G) (fun _ => Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen T G ⊤
        (isAffineOpen_top T) 1 one_pos)
  exact isZero_cohomology_of_retract H.obj Hfree.obj 1 (SheafHom.precomp r.r H Hfree)
    (SheafHom.precomp r.i Hfree H) ((SheafHom.precomp_comp r.i r.r H Hfree H).symm.trans
      ((congrArg (fun β : F ⟶ F => SheafHom.precomp β H H) r.retract).trans
        (SheafHom.precomp_id H))) hfree

end Stacks.Cohomology.Affine

end
