module

public import StacksFrontier.Algebra.Homology.SpectralSequence.LerayOfAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticCohomologyVanishing

/-!
# The Leray spectral sequence of a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `f_*` a right adjoint of the inverse
image `f^* : Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` of **Stacks 06WE** on the fppf sites, at the module universe
`u` of the schemes.  For every bounded below complex `K` of `𝒪_𝒳`-modules there is a spectral
sequence

`E_2^{p,q} = H^p(𝒴, R^q f_* K)  ⟹  H^{p+q}(𝒳, K)`,

the Leray spectral sequence of **Stacks 0732** for the morphism of ringed topoi defined by `f`.

The inverse image is restriction along `f`, hence exact, and it carries `𝒪_𝒴` to `𝒪_𝒳`
(`AlgebraicGeometry.Stack.fppfModulesPullbackUnitIso`), because the structure sheaf of `𝒳` *is*
the restriction of that of `𝒴`.  So `CategoryTheory.Adjunction.exists_leraySpectralSequence`
applies, with `Mod(𝒪)` having enough injectives at `u` by
`AlgebraicGeometry.Stack.enoughInjectives_fppfModules`.  The route is shorter than the source's
for a general morphism of ringed topoi (Stacks 072Z and Stacks 0731): because `f^*` is exact,
`f_*` carries injectives to injectives.

Cohomology `H^p(𝒳, -)` is read as the right derived functors of `Hom(𝒪_𝒳, -)`, i.e. of global
sections; these are the `Ext`-groups `Ext^p(𝒪_𝒳, -)` of
`AlgebraicGeometry.Stack.FlatFppf.fppfModuleCohomology`, and
`AlgebraicGeometry.Stack.isZero_fppfModuleCohomology_iff` translates vanishing between the two
readings.

## Main results

* `AlgebraicGeometry.Stack.exists_fppfLeraySpectralSequence`: the Leray spectral sequence.
* `AlgebraicGeometry.Stack.exists_fppfLeraySpectralSequence_of_isParasitic`: its second page
  read through a coreflection whose counit has parasitic kernel and cokernel.  This is the
  formal skeleton of **Stacks 0782**, delivered in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentLeraySpectralSequence.lean`.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0782](https://stacks.math.columbia.edu/tag/0782)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w t d₁ d₂ d₃

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image of the structure sheaf is the structure sheaf**: `f^* 𝒪_𝒴 ≅ 𝒪_𝒳` for a
1-morphism of algebraic stacks.  The inverse image is restriction along `f` with scalars
transported along the equality of the structure presheaf of `𝒳` with the restriction of that of
`𝒴`, and restriction of scalars along an isomorphism carries the unit to the unit. -/
def fppfModulesPullbackUnitIso :
    (fppfModulesPullback B S hS f).obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (@PresheafOfModules.pushforwardUnitIso _ _ _ _ _ _ _ _
      (inferInstanceAs (IsIso (eqToHom (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        B.topology le_rfl)))))

/-- The inverse image of modules along a 1-morphism of algebraic stacks preserves monomorphisms,
being left exact. -/
instance preservesMonomorphisms_fppfModulesPullback :
    (fppfModulesPullback B S hS f).PreservesMonomorphisms :=
  preservesMonomorphisms_of_preservesLimitsOfShape _

attribute [local instance] enoughInjectives_fppfModules

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{d₁} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{d₂} (fppfModules B S hS 𝒴)] [HasDerivedCategory.{d₃} AddCommGrpCat.{u + 1}]

/-- **The `Ext`-cohomology of an algebraic stack vanishes exactly when the derived global sections
do**: `Ext^i(𝒪_𝒳, F) = 0` if and only if `R^i Hom(𝒪_𝒳, -)(F) = 0`, at whichever universe `t` the
`Ext`-groups are taken.  Both are the right derived functors of global sections, by
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`, and changing the universe of
`Ext` does not change the group, by `CategoryTheory.Abelian.Ext.chgUniv`. -/
theorem isZero_fppfModuleCohomology_iff [HasExt.{t} (fppfModules B S hS 𝒳)]
    (F : fppfModules B S hS 𝒳) (i : ℕ) :
    IsZero ((FlatFppf.fppfModuleCohomology.{u, w, t} B S hS 𝒳 i).obj F) ↔
      IsZero (((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus
        (i : ℤ)).obj F) := by
  let : HasExt.{u + 1} (fppfModules B S hS 𝒳) := HasExt.standard _
  let G := preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)))
  obtain ⟨e⟩ := ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived G _ (Iso.refl _) i
  have h₁ : IsZero ((FlatFppf.fppfModuleCohomology.{u, w, t} B S hS 𝒳 i).obj F) ↔
      IsZero ((Abelian.extFunctorObj.{u + 1} (SheafOfModules.unit _) i).obj F) := by
    simp only [AddCommGrpCat.isZero_iff_subsingleton]
    exact (Abelian.Ext.chgUniv.{u + 1, t}).subsingleton_congr
  exact h₁.trans (e.app F ≪≫ (Stacks.DerivedIndexing.rightDerivedIso G i).app F).isZero_iff

/-- **The Leray spectral sequence of a 1-morphism of algebraic stacks** (Stacks 0732 for the
morphism of ringed topoi it defines).  Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and
`P` a right adjoint of the inverse image `f^*` of modules on the fppf sites, i.e. a direct image
`f_*`.  For every `K` in `D⁺(Mod(𝒪_𝒳))` there is a spectral sequence with
`E_2^{p,q} = H^p(𝒴, H^q(Rf_* K))` abutting to `H^{p+q}(𝒳, K)`, cohomology being read as the right
derived functors of `Hom(𝒪, -)`. -/
theorem exists_fppfLeraySpectralSequence {P : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴}
    (adj : fppfModulesPullback B S hS f ⊣ P) [P.Additive]
    (K : DerivedCategory.Plus (fppfModules B S hS 𝒳)) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor (fppfModules B S hS 𝒴) q).obj
            (P.rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((preadditiveCoyoneda.obj
            (Opposite.op (SheafOfModules.unit _))).rightDerivedFunctorPlus.obj K)) :=
  adj.exists_leraySpectralSequence (fppfModulesPullbackUnitIso B S hS f) K

/-- **The Leray spectral sequence of a 1-morphism of algebraic stacks, with its second page read
through a coreflection with parasitic defect.**  Let `f_*` be a right adjoint of `f^*`, let
`incl ⊣ Q` be a coreflection of `Mod(𝒪_𝒴)` onto a category `𝒬`, and let `M` be an
`𝒪_𝒳`-module.  Suppose that the parasitic `𝒪_𝒴`-modules (**Stacks 0773**) have vanishing
cohomology (`hvanish`), and that the kernel and the cokernel of the counit
`incl (Q (R^q f_* M)) ⟶ R^q f_* M` are parasitic for every `q` (`hker`, `hcoker`).  Then there is
a first quadrant spectral sequence with

`E_2^{p,q} = H^p(𝒴, incl (Q (R^q f_* M)))`

abutting to `H^{p+q}(𝒳, M)`.

This is the argument of **Stacks 0782**, in which `Q` is the coherator, with its three inputs —
Stacks 0779 (2) for the counit and Stacks 0775 (1) for the vanishing — as the hypotheses.  The
tag is delivered, with those inputs proved, in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentLeraySpectralSequence.lean`. -/
theorem exists_fppfLeraySpectralSequence_of_isParasitic
    {P : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴}
    (adj : fppfModulesPullback B S hS f ⊣ P) [P.Additive]
    {𝒬 : Type*} [Category 𝒬] {incl : 𝒬 ⥤ fppfModules B S hS 𝒴}
    {Q : fppfModules B S hS 𝒴 ⥤ 𝒬} (adjQ : incl ⊣ Q) (M : fppfModules B S hS 𝒳)
    [HasExt.{t} (fppfModules B S hS 𝒴)]
    (hvanish : ∀ N : fppfModules B S hS 𝒴, IsParasitic B S hS 𝒴 .fppf N.val → ∀ i : ℕ,
      IsZero ((FlatFppf.fppfModuleCohomology.{u, w, t} B S hS 𝒴 i).obj N))
    (hker : ∀ q : ℕ, IsParasitic B S hS 𝒴 .fppf
      (kernel (adjQ.counit.app ((P.rightDerived q).obj M))).val)
    (hcoker : ∀ q : ℕ, IsParasitic B S hS 𝒴 .fppf
      (cokernel (adjQ.counit.app ((P.rightDerived q).obj M))).val) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℕ, Nonempty ((E.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        ((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus
          (p : ℤ)).obj (incl.obj (Q.obj ((P.rightDerived q).obj M))))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 zero_le_two).X (p, q))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        ((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus n).obj
          M) :=
  have key := fun N hN i => (isZero_fppfModuleCohomology_iff ..).1 (hvanish N hN i)
  adj.exists_leraySpectralSequence_of_coreflection (fppfModulesPullbackUnitIso B S hS f) adjQ M
    (fun q => key _ (hker q)) (fun q => key _ (hcoker q))

end AlgebraicGeometry.Stack
