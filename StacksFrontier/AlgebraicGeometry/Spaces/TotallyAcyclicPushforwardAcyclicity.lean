module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardInjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Totally acyclic modules are acyclic for the direct image along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `𝓜` be an `𝒪_X`-module whose underlying abelian sheaf is totally acyclic in the sense
of Stacks 072Y: its cohomology over every sheaf of sets on the small étale site of `X` vanishes in
positive degrees.  Then `R^n f_*𝓜 = 0` for every `n > 0`.  This is part (4) of Stacks 0731 for the
small étale ringed topoi of algebraic spaces, whose sites have objects in `Type (u + 1)` and
morphisms in `Type u`.

Consequently `R^n (g ≫ f)_* 𝓗 ≅ R^n f_* (g_* 𝓗)` for every morphism `g` and every `𝒪`-module `𝓗`
with vanishing higher direct images along `g` (Stacks 0734 at a module whose `E_2` page has one
row).

## Main results

* `AlgebraicGeometry.Space.isTotallyAcyclic_toSheaf_of_injective_of_modulePushforwardId`: an
  injective `𝒪_X`-module has totally acyclic underlying abelian sheaf.
* `AlgebraicGeometry.Space.epi_modulePushforward_map_of_isTotallyAcyclic`: the direct image of a
  short exact sequence with totally acyclic kernel stays epimorphic on the right.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isTotallyAcyclic`:
  **Stacks 0731 (4)** on small étale sites of algebraic spaces.
* `AlgebraicGeometry.Space.rightDerivedModulePushforwardCompIsoOfAcyclic`: the Leray collapse
  `R^n (g ≫ f)_* 𝓗 ≅ R^n f_* (g_* 𝓗)` when `R^q g_* 𝓗 = 0` for `q > 0`.

## References

* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 21.14.1 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 21.14.5 (Tag 0734)](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtale
  AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite

universe u

namespace AlgebraicGeometry.Space

/-- In a short exact sequence, `Ext` into the quotient vanishes in degree `n` as soon as it
vanishes into the kernel in degree `n + 1` and into the middle term in degree `n`. -/
private lemma subsingleton_ext_X₃_of_shortExact {A : Type*} [Category A] [Abelian A] [HasExt A]
    (T : A) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Ext T S.X₁ (n + 1))) (h₂ : Subsingleton (Ext T S.X₂ n)) :
    Subsingleton (Ext T S.X₃ n) := by
  refine subsingleton_of_forall_eq 0 fun e => ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS e rfl (h₁.elim _ _)
  rw [← hy, h₂.elim y 0, Ext.zero_comp]

/-- A map into the quotient of a short exact sequence lifts to the middle term as soon as `Ext¹`
out of its source into the kernel vanishes. -/
private lemma exists_lift_of_shortExact' {A : Type*} [Category A] [Abelian A] [HasExt A]
    (T : A) {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : Subsingleton (Ext T S.X₁ 1)) (φ : T ⟶ S.X₃) :
    ∃ ψ : T ⟶ S.X₂, ψ ≫ S.g = φ := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ φ) (zero_add 1) (h₁.elim _ _)
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective T S.X₂).2 y
  refine ⟨ψ, (Ext.mk₀_bijective T S.X₃).1 ?_⟩
  rwa [← Ext.mk₀_comp_mk₀]

/-- Every object is the kernel of a short exact sequence with injective middle term. -/
private lemma exists_shortExact_of_injective {A : Type*} [Category A] [Abelian A]
    [EnoughInjectives A] (M : A) :
    ∃ T : ShortComplex A, T.ShortExact ∧ Injective T.X₂ ∧ T.X₁ = M :=
  ⟨ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _),
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }, inferInstance, rfl⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An injective `𝒪_X`-module has totally acyclic underlying abelian sheaf.** -/
theorem isTotallyAcyclic_toSheaf_of_injective_of_modulePushforwardId (X : AlgebraicSpaces B S hS)
    (I : Modules.{u, u} B S hS X.1 X.2) (hI : Injective I) :
    Stacks.Cohomology.IsTotallyAcyclic.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
          I) := fun K p hp =>
  subsingleton_ext_of_iso_right
    ((SheafOfModules.toSheaf _).mapIso ((modulePushforwardIdIso B S hS X).app I).symm) p
    (isTotallyAcyclic_modulePushforward_of_injective (hZ := hI) B S hS (𝟙 X) I K p hp)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The direct image keeps a short exact sequence with totally acyclic kernel epimorphic on
the right.** -/
theorem epi_modulePushforward_map_of_isTotallyAcyclic (f : X ⟶ Y)
    {T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)} (hT : T.ShortExact)
    (h₁ : Stacks.Cohomology.IsTotallyAcyclic.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).J
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
          T.X₁)) :
    Epi ((modulePushforward B S hS f).map T.g) := by
  let J := (smallEtaleRingedSite B S hS X.1 X.2).J
  let Ab := SheafOfModules.toSheaf
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have hAb : (T.map Ab).ShortExact := hT.map_of_exact Ab
  let K : Sheaf J (Type u) := (sheafCompose J (forget AddCommGrpCat.{u})).obj (Ab.obj T.X₃)
  let adj := Presheaf.freeAbelianSheafAdj.{u} J
  let a : (Presheaf.freeAbelianSheaf J).obj K.obj ⟶ Ab.obj T.X₃ :=
    (adj.homEquiv K.obj (Ab.obj T.X₃)).symm (𝟙 K.obj)
  obtain ⟨b, hb⟩ := exists_lift_of_shortExact' ((Presheaf.freeAbelianSheaf J).obj K.obj) hAb
    (h₁ K 1 le_rfl) a
  let s : SplitEpi ((sheafCompose J (forget AddCommGrpCat.{u})).map (Ab.map T.g)) := by
    refine ⟨⟨adj.homEquiv K.obj (Ab.obj T.X₂) b⟩, ?_⟩
    apply Sheaf.hom_ext
    change adj.homEquiv K.obj (Ab.obj T.X₂) b ≫
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian).map (Ab.map T.g) =
      𝟙 K.obj
    rw [← adj.homEquiv_naturality_right]
    change adj.homEquiv K.obj (Ab.obj T.X₃) (b ≫ (T.map Ab).g) = 𝟙 K.obj
    rw [hb]
    exact (adj.homEquiv K.obj (Ab.obj T.X₃)).apply_symm_apply (𝟙 K.obj)
  let P : Sheaf J AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u} :=
    Stacks.Topos.AbelianPushforward.abelianPushforward J (smallToposMorphismTypeU B S hS f)
  have h2 : Epi (P.map (Ab.map T.g)) :=
    (sheafCompose (smallEtaleRingedSite B S hS Y.1 Y.2).J (forget AddCommGrpCat.{u})).epi_of_epi_map
      (s.map (smallToposMorphismTypeU B S hS f).pushforward).epi
  let e := toSheafModulePushforwardIso B S hS f
  have h3 : Epi ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).map
        ((modulePushforward B S hS f).map T.g)) := by
    rw [show (SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).map
          ((modulePushforward B S hS f).map T.g) =
        (e.app T.X₂).hom ≫ P.map (Ab.map T.g) ≫ (e.app T.X₃).inv from
      (NatIso.naturality_2 e T.g).symm]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' h2 (IsIso.epi_of_iso _))
  have hfaith : (SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Faithful :=
    inferInstance
  have := @Functor.reflectsEpimorphisms_of_faithful _ _ _ _ _ hfaith
  exact Functor.epi_of_epi_map (SheafOfModules.toSheaf.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) h3

/-- **Stacks 0731, part (4), on the small étale sites of algebraic spaces.**  Let `f : X ⟶ Y` be
a morphism of algebraic spaces and let `𝓜` be an `𝒪_X`-module whose underlying abelian sheaf is
totally acyclic.  Then `R^{n+1} f_* 𝓜 = 0` for every `n`. -/
theorem isZero_rightDerived_modulePushforward_of_isTotallyAcyclic (f : X ⟶ Y) (n : ℕ) :
    ∀ (M : Modules.{u, u} B S hS X.1 X.2),
      Stacks.Cohomology.IsTotallyAcyclic.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).J
        ((SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
            M) →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS f).rightDerived (n + 1)).obj M) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  induction n with
  | zero =>
    intro M hM
    obtain ⟨T, hT, hI, rfl⟩ := exists_shortExact_of_injective M
    have hg : Epi (((modulePushforward B S hS f).rightDerived 0).map T.g) := by
      rw [← NatIso.naturality_2 (modulePushforward B S hS f).rightDerivedZeroIsoSelf T.g]
      exact epi_comp' (IsIso.epi_of_iso _) (epi_comp'
        (epi_modulePushforward_map_of_isTotallyAcyclic B S hS f hT hM) (IsIso.epi_of_iso _))
    exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hT _ 0 hg
      ((modulePushforward B S hS f).isZero_rightDerived_obj_injective_succ 0 T.X₂)
  | succ n ih =>
    intro M hM
    obtain ⟨T, hT, hI, rfl⟩ := exists_shortExact_of_injective M
    have hQ : Stacks.Cohomology.IsTotallyAcyclic.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).J
        ((SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
            T.X₃) := fun K p hp =>
      subsingleton_ext_X₃_of_shortExact _ (hT.map_of_exact (SheafOfModules.toSheaf _)) p
        (hM K (p + 1) (by omega))
        (isTotallyAcyclic_toSheaf_of_injective_of_modulePushforwardId B S hS X T.X₂
          hI K p hp)
    exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_injective hT _ n
      (ih T.X₃ hQ)

/-- **The direct image of an injective module is acyclic for every further direct image**
(Stacks 072Z with Stacks 0731 (4)): for `g : W ⟶ X`, `f : X ⟶ Y` and an injective
`𝒪_W`-module `𝓘`, `R^n f_* (g_* 𝓘) = 0` for `n > 0`. -/
theorem isZero_rightDerived_modulePushforward_modulePushforward_of_injective
    {W : AlgebraicSpaces B S hS} (g : W ⟶ X) (f : X ⟶ Y) (I : Modules.{u, u} B S hS W.1 W.2)
    (hI : Injective I) (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived n).obj
      ((modulePushforward B S hS g).obj I)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact isZero_rightDerived_modulePushforward_of_isTotallyAcyclic B S hS f m _
    (isTotallyAcyclic_modulePushforward_of_injective (hZ := hI) B S hS g I)

/-- **The Leray collapse along an arbitrary morphism** (Stacks 0734, at a module whose `E_2` page
is concentrated in one row).  For morphisms `g : U ⟶ X` and `f : X ⟶ Y` of algebraic spaces and
an `𝒪_U`-module `𝓗` with `R^q g_* 𝓗 = 0` for every `q > 0`,

`R^n (g ≫ f)_* 𝓗 ≅ R^n f_* (g_* 𝓗)` for every `n`. -/
def rightDerivedModulePushforwardCompIsoOfAcyclic {U : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (f : X ⟶ Y) (H : Modules.{u, u} B S hS U.1 U.2)
    (hH : have := hasInjectiveResolutions_modules B S hS U.1 U.2
      ∀ q, 0 < q → IsZero (((modulePushforward B S hS g).rightDerived q).obj H)) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS U.1 U.2
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS (g ≫ f)).rightDerived n).obj H ≅
      ((modulePushforward B S hS f).rightDerived n).obj ((modulePushforward B S hS g).obj H) :=
  have := hasInjectiveResolutions_modules B S hS U.1 U.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS g
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS (g ≫ f)
  (Functor.rightDerivedIsoOfNatIso (modulePushforwardCompIso B S hS g f).symm n).app H ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (modulePushforward B S hS g)
      (modulePushforward B S hS f) hH
      (isZero_rightDerived_modulePushforward_modulePushforward_of_injective B S hS g f) n

end AlgebraicGeometry.Space

end
