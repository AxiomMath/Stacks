module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
import StacksCore.Tactic.StacksAttribute

/-!
# A totally acyclic sheaf of modules is acyclic for a direct image

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `N` be a sheaf of
`O_C`-modules whose underlying abelian sheaf is totally acyclic in the sense of Stacks 072Y:
its cohomology over every sheaf of sets on `C` vanishes in positive degrees. Then `N` is right
acyclic for the direct image `f_* : Mod(O_C) ⥤ Mod(O_D)`. This is part (4) of Stacks 0731, the
companion of part (3) — right acyclicity for global sections — proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicGlobalSections.lean`.

The source proves part (4) by replacing the morphism of ringed topoi by a morphism of ringed
sites and reading off the description of the higher direct images. The proof given here is a
different one, which stays inside the topos: the totally acyclic modules form a class *adapted*
to `f_*` in the sense of Stacks 05T8, and Stacks 05T8 says that every object of an adapted class
is acyclic. Of the three conditions of that criterion,

* every module embeds in a totally acyclic one, because an injective module is totally acyclic
  (`isTotallyAcyclic_of_injective`, which is the first step of the proof of Stacks 072Z read on
  the identity morphism);
* total acyclicity passes from the kernel and the middle term of a short exact sequence to its
  quotient (`isTotallyAcyclic_of_shortExact`), by the covariant long exact sequence of `Ext`;
* and the direct image of such a short exact sequence is again short exact. Left exactness of
  `f_*` is the adjunction `f^* ⊣ f_*` of Stacks 03D7, and the quotient map stays epimorphic
  because the sequence *splits* after passing to the underlying sheaves of sets
  (`splitEpi_moduleSheafFunctor`): a splitting is a map out of the third term, i.e. — through
  the free abelian sheaf adjunction — a map out of the free abelian sheaf it generates, and
  total acyclicity of the kernel makes `Ext^1` out of that free abelian sheaf vanish, so the map
  lifts. Every functor preserves split epimorphisms.

## Main results

* `Stacks.Cohomology.isTotallyAcyclic_of_injective`: an injective sheaf of modules has totally
  acyclic underlying abelian sheaf.
* `Stacks.Cohomology.isTotallyAcyclic_of_shortExact`: total acyclicity passes to the quotient of
  a short exact sequence of abelian sheaves whose other two terms are totally acyclic.
* `Stacks.Cohomology.splitEpi_moduleSheafFunctor`: a short exact sequence of sheaves of modules
  with totally acyclic kernel splits on the underlying sheaves of sets. The same splitting
  serves parts (1) and (2) of the tag, in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicSections.lean`.
* `Stacks.Cohomology.hasRightDerivedFunctor_pushforwardModules`: the direct image of modules has
  a right derived functor, from the enough injectives of the source category.
* `Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic`: **Stacks 0731,
  part (4)**, a module with totally acyclic underlying abelian sheaf is right acyclic for the
  direct image along a morphism of ringed topoi.

## Implementation notes

The two ringed topoi have all of their universes equal, as in the source of Stacks 072Z. The
reason is twofold: `ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree`, the `Ext`-vanishing
which makes an injective module totally acyclic, is available only for a small site with its
sheaves valued in the same universe; and the abelian structure of `SheafOfModules.{w} R` for
`R` a sheaf of rings on a site with object universe `u` and morphism universe `v` requires
`w = max u v w`. The universe of the `Ext`-groups witnessing total acyclicity stays
independent, as it is in `Stacks.Cohomology.IsTotallyAcyclic`; it is changed to the sheaf
universe with `Abelian.Ext.chgUniv` where the torsion-free vanishing needs it.

Right acyclicity is obtained from the adapted-class criterion of Stacks 05T8
(`CategoryTheory.Functor.le_rightAcyclic`) rather than from an injective resolution, so no
comparison of the two models of the higher right derived functors intervenes.

Enough injectives for sheaves of modules is proved, not assumed: `SheafOfModules.{u} R` on a
small site is Grothendieck abelian (Mathlib's `SheafOfModules.instIsGrothendieckAbelian`,
generalized to independent universes by `SheafOfModules.isGrothendieckAbelian_of_univLE`) and a
Grothendieck abelian category has enough injectives. The same holds for injective resolutions of
the abelian sheaves, through `Sheaf.instIsGrothendieckAbelian`. That is what produces the
embedding of a module in an injective — hence in a totally acyclic — one, which is the first
condition of Stacks 05T8, and also the `HasRightDerivedFunctor` instance that stating
`Functor.rightAcyclic` requires. So the only hypothesis on the module is the total acyclicity
the source assumes.

The underlying sheaf of sets of a direct image of modules *is* the direct image of the
underlying sheaf of sets — `Stacks.Sheaves.RingedToposModules.moduleSheaf_pushforwardModules`
is `rfl` — and the same holds for the two functors, so the split epimorphism produced on the
source topos is carried to the target by `CategoryTheory.SplitEpi.map` with no comparison
isomorphism to insert. Epimorphy is brought back to sheaves of modules by
`CategoryTheory.Sheaf.moduleSheafFunctor` reflecting epimorphisms.

## References

* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 13.15.6 (Tag 05T8)](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

universe x u

namespace Stacks.Cohomology

/-! ### Dévissage for `Ext` out of a fixed object -/

/-- The kernel and the middle term of a short exact sequence control the quotient: if `Ext` out
of `T` vanishes in degree `n + 1` on the kernel and in degree `n` on the middle term, then it
vanishes in degree `n` on the quotient. This is the covariant long exact sequence of `Ext`. -/
private lemma subsingleton_ext_of_shortExact {A : Type*} [Category A] [Abelian A] [HasExt.{x} A]
    (T : A) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Ext.{x} T S.X₁ (n + 1)))
    (h₂ : Subsingleton (Ext.{x} T S.X₂ n)) :
    Subsingleton (Ext.{x} T S.X₃ n) := by
  refine subsingleton_of_forall_eq 0 fun e ↦ ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS e rfl (h₁.elim _ _)
  rw [← hy, h₂.elim y 0, Ext.zero_comp]

/-- A map into the quotient of a short exact sequence lifts to the middle term as soon as `Ext`
out of its source vanishes in degree one on the kernel: the obstruction to lifting is the image
of the map under the connecting map of the covariant long exact sequence. -/
private lemma exists_lift_of_shortExact {A : Type*} [Category A] [Abelian A] [HasExt.{x} A]
    (T : A) {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : Subsingleton (Ext.{x} T S.X₁ 1)) (φ : T ⟶ S.X₃) :
    ∃ ψ : T ⟶ S.X₂, ψ ≫ S.g = φ := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ φ) (zero_add 1) (h₁.elim _ _)
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective T S.X₂).2 y
  exact ⟨ψ, (Ext.mk₀_bijective T S.X₃).1 (by rwa [← Ext.mk₀_comp_mk₀])⟩

/-! ### The class of totally acyclic modules -/

/-- An injective sheaf of modules has totally acyclic underlying abelian sheaf. Cohomology over
a sheaf of sets is `Ext` out of the free abelian sheaf it generates, that sheaf is sectionwise
torsion free, and `Ext` out of a sectionwise torsion-free abelian sheaf into the abelian sheaf
underlying an injective module vanishes in positive degree
(`ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree`). -/
theorem isTotallyAcyclic_of_injective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{u})]
    (R : Sheaf J RingCat.{u}) (I : SheafOfModules.{u} R) [Injective I] :
    IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj I) := by
  intro K p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hTF : ∀ U, Module.IsTorsionFree ℤ
      (((Presheaf.freeAbelianSheaf J).obj K.obj).obj.obj U) := fun U ↦
    ModuleSheafCohomology.isTorsionFree_sheafify J (K.obj ⋙ AddCommGrpCat.free) (fun V ↦ by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup (K.obj.obj V))
      exact Module.Flat.isTorsionFree) U
  have : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := inferInstance
  have : Subsingleton (Ext.{u} ((Presheaf.freeAbelianSheaf J).obj K.obj)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :=
    subsingleton_of_forall_eq 0 (ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree J R I _ hTF n)
  exact Ext.chgUniv.{u, x}.subsingleton

/-- Total acyclicity passes from the kernel and the middle term of a short exact sequence of
abelian sheaves to its quotient. -/
theorem isTotallyAcyclic_of_shortExact {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{u})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic J S.X₁) (h₂ : IsTotallyAcyclic J S.X₂) :
    IsTotallyAcyclic J S.X₃ := fun K p hp ↦
  subsingleton_ext_of_shortExact _ hS p (h₁ K (p + 1) (by omega)) (h₂ K p hp)

/-- A short exact sequence of sheaves of modules whose kernel has totally acyclic underlying
abelian sheaf splits after passing to the underlying sheaves of sets. A splitting is a map from
the underlying sheaf of sets of the third term to that of the second; by the free abelian sheaf
adjunction such maps are maps of abelian sheaves out of the free abelian sheaf generated by it,
and total acyclicity of the kernel makes `Ext^1` out of that free abelian sheaf vanish, so the
identity lifts across the epimorphism. -/
lemma splitEpi_moduleSheafFunctor {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{u})]
    [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
    (R : Sheaf J RingCat.{u})
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₁)) :
    Nonempty (SplitEpi ((Sheaf.moduleSheafFunctor R).map S.g)) := by
  let toAb := SheafOfModules.toSheaf.{u} R
  let forgetAb := sheafCompose J (forget AddCommGrpCat.{u})
  let K : Sheaf J (Type u) := forgetAb.obj (toAb.obj S.X₃)
  let adj := Presheaf.freeAbelianSheafAdj.{u} J
  let a : (Presheaf.freeAbelianSheaf J).obj K.obj ⟶ toAb.obj S.X₃ :=
    (adj.homEquiv K.obj (toAb.obj S.X₃)).symm (𝟙 K.obj)
  obtain ⟨b, hb⟩ := exists_lift_of_shortExact
    ((Presheaf.freeAbelianSheaf J).obj K.obj) (hS.map_of_exact toAb) (h₁ K 1 le_rfl) a
  refine ⟨⟨⟨adj.homEquiv K.obj (toAb.obj S.X₂) b⟩, ?_⟩⟩
  apply Sheaf.hom_ext
  show adj.homEquiv K.obj (toAb.obj S.X₂) b ≫
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian).map (toAb.map S.g) = 𝟙 K.obj
  rw [← adj.homEquiv_naturality_right]
  show adj.homEquiv K.obj (toAb.obj S.X₃) (b ≫ (S.map toAb).g) = 𝟙 K.obj
  rw [hb]
  exact (adj.homEquiv K.obj (toAb.obj S.X₃)).apply_symm_apply (𝟙 K.obj)

/-! ### Part (4) of Stacks 0731 -/

section DirectImage

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasExt.{x} (Sheaf X.J AddCommGrpCat.{u})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The direct image of a short exact sequence of sheaves of modules whose kernel has totally
acyclic underlying abelian sheaf is short exact. Left exactness of the direct image is the
adjunction `f^* ⊣ f_*` of Stacks 03D7, and the quotient map stays epimorphic because the
sequence splits on the underlying sheaves of sets, where every functor preserves split
epimorphisms. -/
private lemma shortExact_map_pushforwardModules
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic X.J
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj S.X₁)) :
    (S.map (pushforwardModules f)).ShortExact := by
  have : PreservesLimitsOfSize.{0, 0} (pushforwardModules f) :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      f).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (pushforwardModules f) := inferInstance
  obtain ⟨hexact, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (pushforwardModules f)).mp inferInstance S hS
  obtain ⟨hsplit⟩ := splitEpi_moduleSheafFunctor X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) S hS h₁
  have hepi : Epi ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((pushforwardModules f).map S.g)) :=
    (hsplit.map f.toToposHom.pushforward).epi
  exact ShortComplex.ShortExact.mk' hexact hmono
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).epi_of_epi_map hepi)

/-- **The direct image of modules has a right derived functor.** Sheaves of modules on a site
have enough injectives, being a Grothendieck abelian category, so every object of `K⁺` of them
has a pointwise right derived functor for any functor out of it; speaking of right acyclicity
for `f_*` therefore needs no existence hypothesis.

The functor is passed to `HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso`
explicitly: left to unification, the same instance exhausts the heartbeat budget. -/
theorem hasRightDerivedFunctor_pushforwardModules
    [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] :
    ((pushforwardModules f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  have := HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
    ((pushforwardModules f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  inferInstance

attribute [local instance] hasRightDerivedFunctor_pushforwardModules

/-- **Stacks 0731, part (4).** A sheaf of modules whose underlying abelian sheaf is totally
acyclic is right acyclic for the direct image along a morphism of ringed topoi. -/
@[stacks 0731 "part (4): direct images", sga "4 V 5.2" "totally acyclic modules"]
theorem rightAcyclic_pushforwardModules_of_isTotallyAcyclic
    [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hN : IsTotallyAcyclic X.J
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N)) :
    (pushforwardModules f).rightAcyclic N :=
  Functor.le_rightAcyclic (pushforwardModules f)
    (fun M ↦ IsTotallyAcyclic X.J
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
    (fun M ↦ ⟨Injective.under M,
      isTotallyAcyclic_of_injective X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (Injective.under M),
      Injective.ι M, inferInstance⟩)
    (fun S hS h₁ h₂ ↦ ⟨isTotallyAcyclic_of_shortExact X.J
        (hS.map_of_exact
          (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) h₁ h₂,
      shortExact_map_pushforwardModules f S hS h₁⟩) N hN

end DirectImage

end Stacks.Cohomology

end
