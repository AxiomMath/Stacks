module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AdjointExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing

/-!
# The derived lower shriek of modules for the projection of a fibred category

Let `(D, O_D)` be a ringed site and `p : C ⥤ D` a fibred category, with `C` carrying the
inherited topology, as in Stacks 08P8, and let `π : Sh(C) ⟶ Sh(D)` be the induced morphism of
topoi. For a sheaf of rings `O` on `D` set `O_C = π⁻¹ O`. This file proves the acyclicity
statement of Stacks 07AC for the lower shriek `π_! : Mod(O_C) ⥤ Mod(O)`, so that the left
derived functor `Lπ_! : D(O_C) ⥤ D(O)` exists and is left adjoint to `π^*`, as Stacks 08PC (3)
asserts, with no hypothesis.

The proof is the one of Stacks 07AC: for an injective `O`-module `I`,
`Ext^n_{O_C}(j_{U!} O_U, π^* I) = 0` for `n ≥ 1` and every object `U` of `C`, and then
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules_acyclic`'s argument applies verbatim.
The vanishing is obtained without the Čech computation of Stacks 0D6X, which needs fibre
products in `D`, through three transfers of `Ext` along exact functors
(`Stacks.Cohomology.subsingleton_ext_iff_of_exact`):

* forgetting the module structure, with `j_{U!} O_U` going to `j_{U!} ℤ_U`. The underlying abelian
  sheaf of an injective module is not injective, but it is `Ext`-acyclic against the
  sectionwise torsion-free sheaf `j_{U!} ℤ_U`, which is the input of Stacks 03FD;
* restriction along the strongly cartesian lifts at `U`, the composite of `j_U⁻¹` and the
  inverse image of the section of Stacks 08P9, which carries `π⁻¹ G` to `G|_{p(U)}`;
* restriction `j_{p(U)}⁻¹` to the localized base.

Together they give `Ext^n(j_{U!} ℤ_U, π⁻¹ G) = 0 ↔ Ext^n(j_{p(U)!} ℤ_{p(U)}, G) = 0` for every
abelian sheaf `G` on `D`, and the right-hand side vanishes for the underlying sheaf of an
injective `O`-module, again by Stacks 03FD.

## Main results

* `Stacks.Cohomology.subsingleton_ext_iff_of_exact`: `Ext` out of an object transported
  along an exact functor that identifies the morphisms out of it.

The others are in the namespace `Stacks.Sites.FibredCategory.FibredCategorySituation`:

* `subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage_iff`: the cohomology of `π⁻¹ G`
  over `U` vanishes in a positive degree exactly when that of `G` over `p(U)` does.
* `subsingleton_ext_extensionByZeroUnit_iff`: Stacks 03FD for the `Ext` out of `j_{U!} O_U`.
* `lowerShriekModules_acyclic_anyUniverse`: the acyclicity statement of Stacks 07AC for `π_!` on
  modules.
* `hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy_anyUniverse`: the existence of `Lπ_!`, as
  an instance.
* `derivedModuleLowerShriek` and `derivedModuleLowerShriekAdjunction`: `Lπ_!` and the
  adjunction `Lπ_! ⊣ π^*` of Stacks 08PC (3).

## Implementation notes

The modules are taken in `max w uD vD uC vC`, the universe in which Stacks 08P8 forms `π`, for
an arbitrary sheaf of rings `O` on the base in that universe. That universe contains both sites,
which is what makes sheafification, Grothendieck abelianness and the smallness of `C` available,
and it is the universe of the abelian sheaves of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriekAcyclic.lean`,
whose restriction along the cartesian lifts is reused here. The case in which all five universes
of the situation agree is `lowerShriekModules_acyclic` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionDerivedForget.lean`; the
situations of polynomial charts over a scheme or an algebraic space have a large total category,
so they need the statements here.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

universe t t'

section ExtTransfer

variable {A : Type*} [Category* A] [Abelian A] [HasExt.{t} A]

/-- For a short exact sequence whose middle term has no first `Ext` out of `X`, the first `Ext`
out of `X` into the first term vanishes exactly when every morphism from `X` to the last term
lifts to the middle term. -/
theorem subsingleton_ext_one_iff_forall_lift (X : A) {S : ShortComplex A} (hS : S.ShortExact)
    (h₂ : Subsingleton (Abelian.Ext X S.X₂ 1)) :
    Subsingleton (Abelian.Ext X S.X₁ 1) ↔ ∀ q : X ⟶ S.X₃, ∃ h : X ⟶ S.X₂, h ≫ S.g = q := by
  refine ⟨fun _ q => ?_, fun hlift => subsingleton_of_forall_eq 0 fun z => ?_⟩
  · obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS (Abelian.Ext.mk₀ q)
      (zero_add 1) (Subsingleton.elim _ _)
    refine ⟨Abelian.Ext.homEquiv₀ x₂, (Abelian.Ext.mk₀_bijective X S.X₃).1 ?_⟩
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply, hx₂]
  · obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS z (Subsingleton.elim _ _)
      (zero_add 1)
    obtain ⟨h, hh⟩ := hlift (Abelian.Ext.homEquiv₀ q)
    rw [← hq, show q = Abelian.Ext.mk₀ (h ≫ S.g) by rw [hh, Abelian.Ext.mk₀_homEquiv₀_apply],
      ← Abelian.Ext.mk₀_comp_mk₀_assoc]
    simp

/-- For a short exact sequence whose middle term has no `Ext` out of `X` in degrees `n` and
`n + 1`, the `Ext` out of `X` into the first term vanishes in degree `n + 1` exactly when the
`Ext` out of `X` into the last term vanishes in degree `n`. -/
theorem subsingleton_ext_succ_iff (X : A) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Abelian.Ext X S.X₂ n))
    (h₂' : Subsingleton (Abelian.Ext X S.X₂ (n + 1))) :
    Subsingleton (Abelian.Ext X S.X₁ (n + 1)) ↔ Subsingleton (Abelian.Ext X S.X₃ n) := by
  refine ⟨fun _ => subsingleton_of_forall_eq 0 fun q => ?_,
    fun _ => subsingleton_of_forall_eq 0 fun z => ?_⟩
  · obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS q rfl (Subsingleton.elim _ _)
    rw [← hx₂, Subsingleton.elim x₂ 0, Abelian.Ext.zero_comp]
  · obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS z (Subsingleton.elim _ _) rfl
    rw [← hq, Subsingleton.elim q 0, Abelian.Ext.zero_comp]

/-- A functor preserving injective objects carries an injective object to one with no
positive `Ext` out of any object. -/
theorem subsingleton_ext_map_of_injective {B : Type*} [Category* B] (R : B ⥤ A)
    [R.PreservesInjectiveObjects] (X' : A) (I : B) (hI : Injective I) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext X' (R.obj I) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have := R.injective_obj I
  exact Abelian.Ext.subsingleton_of_injective _ _ m

variable {B : Type*} [Category* B] [Abelian B] [HasExt.{t'} B] [EnoughInjectives B]

/-- **`Ext` out of an object transported along an exact functor.** Let `R : B ⥤ A` be an exact
functor between abelian categories, `B` having enough injectives, and let `X : B` and `X' : A`
be such that the morphisms out of `X` are, naturally, the morphisms out of `X'` into the image
under `R`. If `R` carries injective objects to objects with no positive `Ext` out of `X'`, then
for every `n ≥ 1` and every `Y`, `Ext^n(X, Y)` vanishes exactly when `Ext^n(X', R Y)` does.

Embed `Y` in an injective object with cokernel `Q`; `R` keeps the sequence short exact. In
degree one both groups vanish exactly when every morphism out of `X`, respectively `X'`, into
`Q`, respectively `R Q`, lifts, and the natural identification makes the two lifting conditions
the same. In degree `n + 1 ≥ 2` both groups are the degree-`n` groups into `Q` and `R Q`, and
induction applies. The universes of the two `Ext` groups are independent. -/
theorem subsingleton_ext_iff_of_exact (R : B ⥤ A) [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (X : B) (X' : A) (e : ∀ Y : B, (X ⟶ Y) ≃ (X' ⟶ R.obj Y))
    (he : ∀ {Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), e Z (f ≫ g) = e Y f ≫ R.map g)
    (hinj : ∀ I : B, Injective I → ∀ n : ℕ, 1 ≤ n →
      Subsingleton (Abelian.Ext X' (R.obj I) n))
    (n : ℕ) (hn : 1 ≤ n) (Y : B) :
    Subsingleton (Abelian.Ext X Y n) ↔ Subsingleton (Abelian.Ext X' (R.obj Y) n) := by
  induction n generalizing Y with
  | zero => omega
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation Y
    let S := ShortComplex.mk ip.f (cokernel.π ip.f) (cokernel.condition ip.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ip.f }
    have hS' : (S.map R).ShortExact := hS.map_of_exact R
    have : Injective S.X₂ := ip.injective
    rcases n with _ | n
    · refine (subsingleton_ext_one_iff_forall_lift X hS
        (Abelian.Ext.subsingleton_of_injective _ _ 0)).trans
          (Iff.trans ?_ (subsingleton_ext_one_iff_forall_lift X' hS'
            (hinj _ ip.injective 1 le_rfl)).symm)
      refine ⟨fun hl q' => ?_, fun hl q => ?_⟩
      · obtain ⟨h, hh⟩ := hl ((e S.X₃).symm q')
        refine ⟨e S.X₂ h, ?_⟩
        change e S.X₂ h ≫ R.map S.g = q'
        rw [← he, hh, Equiv.apply_symm_apply]
      · obtain ⟨h', hh'⟩ := hl (e S.X₃ q)
        refine ⟨(e S.X₂).symm h', (e S.X₃).injective ?_⟩
        rwa [he, Equiv.apply_symm_apply]
    · exact (subsingleton_ext_succ_iff X hS (n + 1)
        (Abelian.Ext.subsingleton_of_injective _ _ n)
        (Abelian.Ext.subsingleton_of_injective _ _ (n + 1))).trans
          ((ih (by omega) S.X₃).trans (subsingleton_ext_succ_iff X' hS' (n + 1)
            (hinj _ ip.injective _ (by omega)) (hinj _ ip.injective _ (by omega))).symm)

/-- `subsingleton_ext_iff_of_exact`, with the identification of morphisms out of `X` and `X'` given
as two identifications with a common type of "sections" `τ`, each natural in its own sense. -/
private theorem subsingleton_ext_iff_of_exact_of_sections (R : B ⥤ A) [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (X : B) (X' : A) {τ : A → Type*}
    (e₁ : ∀ Y : B, (X ⟶ Y) ≃ τ (R.obj Y)) (e₂ : ∀ Z : A, (X' ⟶ Z) ≃ τ Z)
    (m : ∀ {Y Z : A}, (Y ⟶ Z) → τ Y → τ Z)
    (h₁ : ∀ {Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), e₁ Z (f ≫ g) = m (R.map g) (e₁ Y f))
    (h₂ : ∀ {Y Z : A} (f : X' ⟶ Y) (g : Y ⟶ Z), e₂ Z (f ≫ g) = m g (e₂ Y f))
    (hinj : ∀ I : B, Injective I → ∀ n : ℕ, 1 ≤ n →
      Subsingleton (Abelian.Ext X' (R.obj I) n))
    (n : ℕ) (hn : 1 ≤ n) (Y : B) :
    Subsingleton (Abelian.Ext X Y n) ↔ Subsingleton (Abelian.Ext X' (R.obj Y) n) :=
  subsingleton_ext_iff_of_exact R X X' (fun Y => (e₁ Y).trans (e₂ _).symm)
    (fun {Y Z} f g => by
      apply (e₂ _).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, h₂, h₁]) hinj n hn Y

end ExtTransfer

end Stacks.Cohomology

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w

namespace FibredCategorySituation

open Stacks.Cohomology.DerivedLowerShriek

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- On the total category, sheafification of abelian sheaves in the universe in which `π` is
formed inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijectiveTopology :
    s.topology.WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC vC} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{uC, vC,
    max w uD vD uC vC} (J := s.topology)

/-- On the base site, sheafification of abelian sheaves in the universe in which `π` is formed
inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijectiveBaseTopology :
    s.base.J.WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC vC} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{uD, vD,
    max w uD vD uC vC} (J := s.base.J)

/-- Sheaves of modules on the total category, in the universe in which `π` is formed, form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_totalModules (R : Sheaf s.topology RingCat.{max w uD vD uC vC}) :
    IsGrothendieckAbelian.{max w uD vD uC vC} (SheafOfModules.{max w uD vD uC vC} R) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{max w uD vD uC vC, vC, uC,
    max w uD vD uC vC} R

/-- Sheaves of modules on the base site, in the universe in which `π` is formed, form a
Grothendieck abelian category. -/
instance isGrothendieckAbelian_baseModules (O : Sheaf s.base.J RingCat.{max w uD vD uC vC}) :
    IsGrothendieckAbelian.{max w uD vD uC vC} (SheafOfModules.{max w uD vD uC vC} O) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{max w uD vD uC vC, vD, uD,
    max w uD vD uC vC} O

/-- **The cohomology of `π⁻¹ G` over an object of the total category is the cohomology of `G`
over its image**, in the form of the vanishing of a positive-degree `Ext`:
`Ext^n(j_{U!} ℤ_U, π⁻¹ G)` vanishes exactly when `Ext^n(j_{p(U)!} ℤ_{p(U)}, G)` does.

Both are compared with `Ext^n` out of `j_{T!} ℤ_T` on the localized base `D/p(U)`, `T` its
terminal object: on the total category along the restriction along the strongly cartesian lifts
at `U` (Stacks 08P9), which carries `π⁻¹ G` to `G|_{p(U)}`, and on the base along `j_{p(U)}⁻¹`.
Both functors are exact and preserve injectives, and morphisms out of the free abelian sheaf on
an object are the sections over it, which these restrictions identify. -/
theorem subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage_iff (U : s.C)
    (G : Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext
        (extensionByZeroUnitAb.{max w uD vD uC} s.topology U) (s.abelianInverseImage.obj G) n) ↔
      Subsingleton (Abelian.Ext
        (extensionByZeroUnitAb.{max w uD uC vC} s.base.J (s.p.obj U)) G n) := by
  let A := AddCommGrpCat.{max w uD vD uC vC}
  let K := s.base.J.over (s.p.obj U)
  let T : Over (s.p.obj U) := Over.mk (𝟙 (s.p.obj U))
  let U' := (s.cartesianLiftRestrictionFunctor U).obj T
  have : ∀ V : s.base.C, HasSheafify (s.base.J.over V) A := fun V =>
    hasSheafify_addCommGrpCat.{max uD vD, vD, max w uD vD uC vC} (s.base.J.over V)
  have : IsGrothendieckAbelian.{max w uD vD uC vC} (Sheaf K A) :=
    isGrothendieckAbelian_sheaf_addCommGrpCat.{max uD vD, vD, max w uD vD uC vC} K
  obtain ⟨h₁, h₂, h₃⟩ := s.cartesianLiftRestriction_exact U
  have hC := Stacks.Cohomology.subsingleton_ext_iff_of_exact_of_sections
    (s.cartesianLiftRestriction U) (extensionByZeroUnitAb.{max w uD vD uC} s.topology U')
    (extensionByZeroUnitAb.{max w uD uC vC} K T)
    (τ := fun Z : Sheaf K A => (Z.obj.obj (op T) : Type _))
    (extensionByZeroUnitAbHomEquiv.{max w uD vD uC} s.topology U')
    (extensionByZeroUnitAbHomEquiv.{max w uD uC vC} K T)
    (fun g x => ConcreteCategory.hom (g.hom.app (op T)) x)
    (fun f g => extensionByZeroUnitAbHomEquiv_naturality _ f g)
    (fun f g => extensionByZeroUnitAbHomEquiv_naturality _ f g)
    (Stacks.Cohomology.subsingleton_ext_map_of_injective _ _) n hn (s.abelianInverseImage.obj G)
  have : PreservesFiniteColimits (s.base.J.overPullback A (s.p.obj U)) :=
    Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{vD, uD,
      max w uD vD uC vC} s.base.J (s.p.obj U)
  have : (s.base.J.overPullback A (s.p.obj U)).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{vD, uD,
      max w uD vD uC vC} s.base.J (s.p.obj U)
  have hD := Stacks.Cohomology.subsingleton_ext_iff_of_exact_of_sections
    (s.base.J.overPullback A (s.p.obj U))
    (extensionByZeroUnitAb.{max w uD uC vC} s.base.J (s.p.obj U))
    (extensionByZeroUnitAb.{max w uD uC vC} K T)
    (τ := fun Z : Sheaf K A => (Z.obj.obj (op T) : Type _))
    (extensionByZeroUnitAbHomEquiv.{max w uD uC vC} s.base.J (s.p.obj U))
    (extensionByZeroUnitAbHomEquiv.{max w uD uC vC} K T)
    (fun g x => ConcreteCategory.hom (g.hom.app (op T)) x)
    (fun f g => extensionByZeroUnitAbHomEquiv_naturality _ f g)
    (fun f g => extensionByZeroUnitAbHomEquiv_naturality _ f g)
    (Stacks.Cohomology.subsingleton_ext_map_of_injective _ _) n hn G
  let eU : extensionByZeroUnitAb.{max w uD vD uC} s.topology U ≅
      extensionByZeroUnitAb.{max w uD vD uC} s.topology U' :=
    (Presheaf.freeAbelianSheaf.{max w uD vD uC vC} s.topology).mapIso
      (uliftYoneda.{max w uD vD uC}.mapIso (s.cartesianLiftRestrictionFunctorObjIso U).symm)
  let eG := s.cartesianLiftRestrictionInverseImageIso U G
  exact ((((Abelian.extFunctor n).mapIso eU.symm.op).app
      (s.abelianInverseImage.obj G)).addCommGroupIsoToAddEquiv.subsingleton_congr).trans
    (hC.trans ((((Abelian.extFunctor n).obj
      (op (extensionByZeroUnitAb.{max w uD uC vC} K T))).mapIso
        eG).addCommGroupIsoToAddEquiv.subsingleton_congr.trans hD.symm))

/-- The underlying abelian sheaf of an injective module has no positive `Ext` out of the free
abelian sheaf `j_{U!} ℤ_U`, which is sectionwise torsion free, being the sheafification of a
sectionwise free abelian presheaf (Stacks 03FD). -/
private theorem subsingleton_ext_extensionByZeroUnitAb_toSheaf_obj_of_injective.{a, b, c, z}
    {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max b c}] [J.WEqualsLocallyBijective AddCommGrpCat.{max b c}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max b c})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{max b c})] (R : Sheaf J RingCat.{max b c})
    (I : SheafOfModules.{max b c} R) [Injective I] (U : C) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (Abelian.Ext (extensionByZeroUnitAb.{c} J U) ((SheafOfModules.toSheaf R).obj I) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine subsingleton_of_forall_eq 0 fun e =>
    Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree J R I _ (fun X => ?_) m e
  exact ModuleSheafCohomology.isTorsionFree_sheafify J
    (uliftYoneda.{c}.obj U ⋙ AddCommGrpCat.free) (fun Y => by
      change Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift (Y.unop ⟶ U)))
      exact Module.Flat.isTorsionFree) X

/-- **Stacks 03FD for the generators.** For a sheaf of rings `R` on the total category and a
sheaf of `R`-modules `M`, `Ext^n_R(j_{U!} R_U, M)` vanishes in a positive degree exactly when
`Ext^n(j_{U!} ℤ_U, M)` does, computed on the underlying abelian sheaf.

Forgetting the module structure is exact, and both `j_{U!} R_U` and `j_{U!} ℤ_U` corepresent the
sections over `U` (Stacks 0G1V). The underlying abelian sheaf of an injective module is not
injective, but it has no positive `Ext` out of the sectionwise torsion-free sheaf `j_{U!} ℤ_U`,
which is the input of Stacks 03FD. -/
theorem subsingleton_ext_extensionByZeroUnit_iff
    (R : Sheaf s.topology RingCat.{max w uD vD uC vC}) (U : s.C)
    (M : SheafOfModules.{max w uD vD uC vC} R) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext (extensionByZeroUnit R U) M n) ↔
      Subsingleton (Abelian.Ext (extensionByZeroUnitAb.{max w uD vD uC} s.topology U)
        ((SheafOfModules.toSheaf R).obj M) n) := by
  have := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits s.topology R
  exact Stacks.Cohomology.subsingleton_ext_iff_of_exact_of_sections (SheafOfModules.toSheaf R)
    (extensionByZeroUnit R U) (extensionByZeroUnitAb.{max w uD vD uC} s.topology U)
    (τ := fun Z : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} =>
      (Z.obj.obj (op U) : Type _))
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv s.topology R U)
    (extensionByZeroUnitAbHomEquiv.{max w uD vD uC} s.topology U)
    (fun g x => ConcreteCategory.hom (g.hom.app (op U)) x)
    (fun f g => Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality s.topology R U
      f g)
    (fun f g => extensionByZeroUnitAbHomEquiv_naturality _ f g)
    (fun I _ => subsingleton_ext_extensionByZeroUnitAb_toSheaf_obj_of_injective s.topology R I U)
    n hn M

variable (O : Sheaf s.base.J RingCat.{max w uD vD uC vC})

/-- **Stacks 0D6X for an injective module along the projection of a fibred category.** For an
injective `O`-module `I` on the base, `Ext^n_{O_C}(j_{U!} O_U, π^* I) = 0` for every object `U`
of the total category and every `n ≥ 1`: the generators `j_{U!} O_U` are `Ext`-acyclic for the
adjunction `π_! ⊣ π^*`.

By `subsingleton_ext_extensionByZeroUnit_iff` this is the vanishing of `Ext^n(j_{U!} ℤ_U, π⁻¹ I)`
on the underlying abelian sheaves, by
`subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage_iff` that of
`Ext^n(j_{p(U)!} ℤ_{p(U)}, I)`, and that vanishes because `j_{p(U)!} ℤ_{p(U)}` is sectionwise
torsion free (Stacks 03FD). -/
theorem extAcyclic_extensionByZeroUnit_anyUniverse (U : s.C) :
    (adjunctionModules s.topology s.base.J s.p O).extAcyclic
      (extensionByZeroUnit (inverseImageRing s.topology s.base.J s.p O) U) := by
  intro I _ n hn
  rw [s.subsingleton_ext_extensionByZeroUnit_iff _ U _ n hn]
  change Subsingleton (Abelian.Ext _
    (s.abelianInverseImage.obj ((SheafOfModules.toSheaf O).obj I)) n)
  rw [s.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage_iff U _ n hn]
  exact subsingleton_ext_extensionByZeroUnitAb_toSheaf_obj_of_injective s.base.J O I _ n hn

/-- **The acyclicity statement of Stacks 07AC for modules along the projection of a fibred
category.** For an arbitrary sheaf of rings `O` on the base, in the universe in which `π` is
formed, the lower-shriek functor `π_! : Mod(O_C) ⥤ Mod(O)` carries every bounded above acyclic
complex whose terms are direct sums of the `j_{U!} O_U` to an acyclic complex. As in the source,
this is the `Ext`-acyclicity of the generators for the adjunction `π_! ⊣ π^*`,
`extAcyclic_extensionByZeroUnit_anyUniverse`. -/
theorem lowerShriekModules_acyclic_anyUniverse (a : ℤ)
    (L : CochainComplex
      (SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing s.topology s.base.J s.p O) (L.X n))
    (hLac : L.Acyclic) :
    (((lowerShriekModules s.topology s.base.J s.p O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine (adjunctionModules s.topology s.base.J s.p O).map_acyclic_of_extAcyclic L a hLac
    fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (adjunctionModules s.topology s.base.J s.p O).extAcyclic_of_iso e
    ((adjunctionModules s.topology s.base.J s.p O).extAcyclic_coproduct _
      fun i => s.extAcyclic_extensionByZeroUnit_anyUniverse O (U i))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for modules along the projection of a fibred category**, existence, with no
hypothesis: the left derived functor `Lπ_!` of degreewise lower shriek exists at every
object. -/
instance hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy_anyUniverse :
    (lowerShriekOnHomotopy s.topology s.base.J s.p O ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (sourceQuasiIso s.topology s.base.J s.p O) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE s.topology s.base.J s.p O
    (s.lowerShriekModules_acyclic_anyUniverse O)

/-- `Lπ_!` stays a left derived functor after composition with derived restriction, being
constructed by resolutions. -/
instance isLeftDerivedFunctor_derivedLowerShriek_comp_derivedRestriction :
    (derivedLowerShriek s.topology s.base.J s.p O ⋙
      derivedRestriction s.topology s.base.J s.p O).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedLowerShriek s.topology s.base.J s.p O)
          (derivedRestriction s.topology s.base.J s.p O)).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison s.topology s.base.J s.p O)
          (derivedRestriction s.topology s.base.J s.p O))
      (sourceQuasiIso s.topology s.base.J s.p O) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic s.topology s.base.J s.p O
    (s.lowerShriekModules_acyclic_anyUniverse O) _

/-- `Lπ_! : D(O_C) ⥤ D(O)`, the left derived functor of the lower shriek of modules along the
projection of a fibred category, for `O_C = π⁻¹ O`. -/
abbrev derivedModuleLowerShriek :
    DerivedCategory
        (SheafOfModules.{max w uD vD uC vC} (inverseImageRing s.topology s.base.J s.p O)) ⥤
      DerivedCategory (SheafOfModules.{max w uD vD uC vC} O) :=
  derivedLowerShriek s.topology s.base.J s.p O

/-- **Stacks 08PC (3) for the projection of a fibred category**: `Lπ_!` is left adjoint to
`π^* = π⁻¹` on the derived categories of modules. This is the derived adjunction of Stacks 07AC
for the continuous and cocontinuous projection. -/
def derivedModuleLowerShriekAdjunction :
    s.derivedModuleLowerShriek O ⊣ derivedRestriction s.topology s.base.J s.p O :=
  derivedLowerShriekAdjunction s.topology s.base.J s.p O

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
