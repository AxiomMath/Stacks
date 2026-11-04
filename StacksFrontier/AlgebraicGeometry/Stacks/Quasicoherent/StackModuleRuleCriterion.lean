module

public import StacksFrontier.Algebra.Homology.SpectralSequence.WeakSerreDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRuleAffineTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRuleCechInduction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.ModuleSmoothCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison

/-!
# The criterion of Stacks 076Z and Stacks 0770

Let `τ` be the étale or the fppf topology and let `M` be a rule assigning to every algebraic stack
`𝒳` over `S` a property of the modules on `𝒳_τ` such that (1) `M_𝒳` is a weak Serre subcategory,
(2) `M` is stable under inverse image along smooth 1-morphisms, (3) `M` is smooth-local, and
(4) the higher direct images between algebraic stacks represented by affine schemes preserve `M`.
Then the higher direct images along every quasi-compact quasi-separated 1-morphism preserve `M`.

## Main results

* `AlgebraicGeometry.Stack.StackModuleRule.hasCechSpectralSequence_stackModuleDirectImageData`:
  the relative Čech spectral sequence of **Stacks 072G** for the direct image at the universe of
  the schemes, descended from the module universe `u + 1` along the universe lift.
* `AlgebraicGeometry.Stack.StackModuleRule.preservesHigherDirectImages_of_hasSmoothBaseChange`:
  the criterion, from the smooth base change of **Stacks 075H** and the comparison of the higher
  direct images at the two module universes.

## Implementation notes

The relative Čech spectral sequence is constructed at module universe `u + 1`
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_moduleCechSpectralSequence`), because the direct
images of **Stacks 072E** are limits indexed by categories with objects in `Type (u + 1)`. The
universe lift `Mod_u ⥤ Mod_{u+1}` is fully faithful and exact with weak Serre essential image, so
a spectral sequence whose first page lies in that essential image descends to `u` together with its
abutment (`CategoryTheory.SpectralSequence.exists_descend_abutsTo`). The first page lies there once
the higher direct images at the two universes are compared, which is the hypothesis `hcomp`.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace StackModuleRule

open AlgebraicStacks

variable (τ : SiteKind)

/-- **The comparison of the higher direct images at the module universes `u` and `u + 1`**: for a
1-morphism `k : 𝒜 ⟶ 𝒞` of algebraic stacks and a degree `q`, the universe lift of `R^q k_*` is
`R^q k_*` of the universe lift. -/
abbrev HigherDirectImageULiftComparison : Prop :=
  ∀ {𝒜 𝒞 : AlgebraicStacks.{u, t} B S hS} (k : 𝒜 ⟶ 𝒞) (q : ℕ),
    Nonempty (stackModuleULift B S hS τ 𝒜 ⋙
        moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒜.val.val.p 𝒞.val.val.p
          𝒜.val.isFiberedInGroupoids 𝒞.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
          (B.baseTopology τ) (B.baseTopology_le_topology τ) q ≅
      stackModuleHigherDirectImage B S hS k τ q ⋙ stackModuleULift B S hS τ 𝒞)

/-- A faithful additive functor reflects zero objects. -/
private theorem isZero_of_isZero_obj {A C : Type*} [Category A] [Category C] [Preadditive A]
    [Preadditive C] (ι : A ⥤ C) [ι.Faithful] [ι.Additive] {X : A} (h : IsZero (ι.obj X)) :
    IsZero X := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  apply ι.map_injective
  rw [ι.map_id, ι.map_zero, h]

variable {B S hS} in
/-- **The relative Čech spectral sequence of Stacks 072G for the direct image at the universe of
the schemes.** Let `g : 𝒱 ⟶ 𝒵` be a surjective smooth 1-morphism of algebraic stacks which is
representable by algebraic spaces and let `h : 𝒵 ⟶ 𝒴`. For a topology `τ` finer than the étale
one and a module `ℱ` on `𝒵_τ` with sections in `u`, the relative Čech spectral sequence of `g`
and `h` exists, for the direct image `AlgebraicGeometry.Stack.stackModuleDirectImageData`. -/
theorem hasCechSpectralSequence_stackModuleDirectImageData
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (hcomp : HigherDirectImageULiftComparison.{u, t} B S hS τ)
    {𝒱 𝒵 𝒴 : AlgebraicStacks.{u, t} B S hS} (g : 𝒱 ⟶ 𝒵)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom) (hsurj : IsSurjective B S hS g)
    (hsm : AlgebraicStacks.IsSmooth B S hS g) (h : 𝒵 ⟶ 𝒴) (F : StackModules B S hS τ 𝒵) :
    HasCechSpectralSequence (stackModuleDirectImageData B S hS τ) g h F := by
  simp only [HasCechSpectralSequence, stackModuleDirectImageData_higherDirectImage]
  let ι𝒴 := stackModuleULift B S hS τ 𝒴
  have hcover : ∀ x : 𝒵.val.val.obj,
      ∃ (z : 𝒱.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor g.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒵.val.val.p τ x := fun x => by
    obtain ⟨z, α, hα⟩ := Stack.exists_etaleLocalLift B S hS g hsurj hsm x
    exact ⟨z, α, associatedTopology_mono B S hS 𝒵.val.val.p hτ _ hα⟩
  obtain ⟨E, hpage, hzero, habuts⟩ := exists_moduleCechSpectralSequence B S hS g h τ hrep hcover
    ((stackModuleULift B S hS τ 𝒵).obj F)
  have : PreservesFiniteLimits ι𝒴 := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  have : PreservesFiniteColimits ι𝒴 :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift _
  have : ι𝒴.essImage.IsWeakSerreClass :=
    Stacks.SheafOfModules.isWeakSerreClass_essImage_moduleULift _
  have hterm : ∀ p q : ℕ, Nonempty ((E.page 1 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
      ι𝒴.obj ((stackModuleHigherDirectImage B S hS (cechNerveProjection B S hS g p ≫ h) τ q).obj
        ((stackModuleInverseImage B S hS τ (cechNerveProjection B S hS g p)).obj F))) := by
    intro p q
    obtain ⟨e₁⟩ := hpage p q
    obtain ⟨c⟩ := hcomp (cechNerveProjection B S hS g p ≫ h) q
    have heq := moduleInverseImage_eq_modulePullback B S hS
      (cechNerveTerm B S hS g p).val.val.p 𝒵.val.val.p
      (cechNerveTerm B S hS g p).val.isFiberedInGroupoids 𝒵.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor (cechNerveProjection B S hS g p).hom)
      (CatFiberedInGroupoids.homFunctor_comp_p (cechNerveProjection B S hS g p).hom) τ
    exact ⟨e₁ ≪≫ (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS _ _ _ _ _ _
      (B.baseTopology τ) (B.baseTopology_le_topology τ) q).mapIso
        (eqToIso (congrArg (fun G => G.obj ((stackModuleULift B S hS τ 𝒵).obj F)) heq.symm) ≪≫
          ((stackModuleInverseImageULiftIso B S hS (cechNerveProjection B S hS g p) τ).app
            F).symm) ≪≫
      c.app ((stackModuleInverseImage B S hS τ (cechNerveProjection B S hS g p)).obj F)⟩
  have hE : ∀ pq : ℤ × ℤ, ι𝒴.essImage ((E.page 1 le_rfl).X pq) := by
    rintro ⟨p, q⟩
    by_cases hneg : p < 0 ∨ q < 0
    · exact ⟨0, ⟨(ι𝒴.map_isZero (isZero_zero _)).iso (hzero p q hneg)⟩⟩
    · obtain ⟨hp, hq⟩ : 0 ≤ p ∧ 0 ≤ q := by omega
      obtain ⟨e⟩ := hterm p.toNat q.toNat
      rw [Int.toNat_of_nonneg hp, Int.toNat_of_nonneg hq] at e
      exact ⟨_, ⟨e.symm⟩⟩
  obtain ⟨E', H', hpage', hH', habuts'⟩ :=
    SpectralSequence.exists_descend_abutsTo ι𝒴 hE habuts
  refine ⟨E', fun p q => ⟨ι𝒴.preimageIso ((hpage' 1 le_rfl _).some ≪≫ (hterm p q).some)⟩,
    fun p q hpq => isZero_of_isZero_obj ι𝒴
      ((hzero p q hpq).of_iso (hpage' 1 le_rfl (p, q)).some), H', habuts', fun n => ?_⟩
  obtain ⟨c⟩ := hcomp h n
  exact ⟨ι𝒴.preimageIso ((hH' (n : ℤ)).some ≪≫
    eqToIso (by rw [ite_eq_right (by omega), Int.toNat_natCast]; rfl) ≪≫ c.app F)⟩

variable {B S hS} in
/-- **The criterion of Stacks 076Z and Stacks 0770, from its two geometric inputs.** Let `τ` be a
topology finer than the étale one and let `M` be a rule satisfying clauses (1) to (4). Granted the
smooth base change of **Stacks 075H** for the direct image at the universe of the schemes and the
comparison of the higher direct images at the module universes `u` and `u + 1`, the higher direct
images along every quasi-compact quasi-separated 1-morphism of algebraic stacks preserve `M` in
every degree. -/
theorem preservesHigherDirectImages_of_hasSmoothBaseChange
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (hcomp : HigherDirectImageULiftComparison.{u, t} B S hS τ)
    (hbc : HasSmoothBaseChange (stackModuleDirectImageData.{u, t} B S hS τ))
    (M : StackModuleRule.{u, t} B S hS τ) (h1 : IsWeakSerre τ M)
    (h2 : IsStableUnderSmoothPullback τ M) (h3 : IsSmoothLocal.{u, t, u} τ M)
    (h4 : PreservesHigherDirectImagesOfAffine (stackModuleDirectImageData.{u, t} B S hS τ) M) :
    PreservesHigherDirectImages (stackModuleDirectImageData.{u, t} B S hS τ) M :=
  fun f hqc hqs i => preservedBy_of_affineTarget _ M (fun 𝒳 => (h1 𝒳).toIsClosedUnderIsomorphisms)
    h2 h3 hbc i (fun hY f' hqc' hqs' =>
      preservedBy_of_isAffine_of_hasCech _ M h1 h2 h4
        (hasCechSpectralSequence_stackModuleDirectImageData τ hτ hcomp)
        hY f' hqc' hqs' i) f hqc hqs

end StackModuleRule

end AlgebraicGeometry.Stack

end
