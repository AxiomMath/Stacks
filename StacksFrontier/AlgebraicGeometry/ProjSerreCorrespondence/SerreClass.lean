module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantModules
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Exact

/-!
# The quotient of `Mod^fg_A` by the irrelevant modules

Let `A` be a graded ring which is Noetherian as a ring, and let `d` be a positive integer. This
file constructs the quotient category `Mod^fg_A / Mod^fg_{A, irrelevant}` of Tag 0BXF: the
finitely generated graded `A`-modules form an abelian category, the irrelevant ones form a Serre
class in it, and the quotient category is the localization of the one at the other.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isSerreClass_moduleFinite`: over a
  Noetherian ring the finitely generated graded modules are a Serre class among all graded
  modules, so `Mod^fg_A` is an abelian category
  (`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.instAbelianFiniteGradedModules`).
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isSerreClass_irrelevantModules`: the
  irrelevant finitely generated graded modules are a Serre class in `Mod^fg_A`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantQuotient` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.toIrrelevantQuotient`: the quotient category
  `Mod^fg_A / Mod^fg_{A, irrelevant}` of Tag 0BXF together with its quotient functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### `Mod^fg_A` is abelian -/

section Finite

variable [IsNoetherianRing S]

/-- The kernel of a morphism out of a finitely generated graded module, as a finitely generated
graded module. -/
private def finiteKer {X Y : FiniteGradedModules.{u, v, w} 𝒮} (g : X ⟶ Y) :
    FiniteGradedModules.{u, v, w} 𝒮 :=
  have := X.property
  ⟨kerObj g.hom, Module.Finite.of_injective
    (LinearMap.ker g.hom.toLinearMap).subtype Subtype.coe_injective⟩

/-- The inclusion of the kernel of `g`. -/
private def finiteKerι {X Y : FiniteGradedModules.{u, v, w} 𝒮} (g : X ⟶ Y) :
    finiteKer 𝒮 g ⟶ X := ⟨kerι g.hom⟩

/-- The inclusion of the kernel of `g` composes with `g` to zero. -/
private theorem finiteKerι_comp {X Y : FiniteGradedModules.{u, v, w} 𝒮} (g : X ⟶ Y) :
    finiteKerι 𝒮 g ≫ g = 0 := by
  ext
  exact kerι_comp g.hom

/-- Over a Noetherian ring the finitely generated graded modules are a Serre class among all
graded modules. -/
public instance isSerreClass_moduleFinite :
    ObjectProperty.IsSerreClass
      (C := GradedModuleCat.{u, v, w} 𝒮) (fun M => Module.Finite S M.carrier) where
  exists_zero := by
    have hs : Subsingleton (zeroObj.{u, v, w} (𝒮 := 𝒮)).carrier :=
      inferInstanceAs (Subsingleton PUnit.{v + 1})
    refine ⟨zeroObj, isZero_zeroObj, ⟨⟨∅, eq_top_iff.2 fun x _ => ?_⟩⟩⟩
    rw [show x = 0 from hs.elim _ _]
    exact Submodule.zero_mem _
  prop_of_mono {X Y} f hmono hY := by
    have : Module.Finite S Y.carrier := hY
    exact Module.Finite.of_injective f.toLinearMap
      ((GradedModuleCat.mono_iff_injective f).1 hmono)
  prop_of_epi {X Y} f hepi hX := by
    have : Module.Finite S X.carrier := hX
    exact Module.Finite.of_surjective f.toLinearMap
      ((GradedModuleCat.epi_iff_surjective f).1 hepi)
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have : Module.Finite S T.X₁.carrier := h₁
    have : Module.Finite S T.X₃.carrier := h₃
    exact Module.Finite.of_exact (exact_of_shortExact hT)
      ((GradedModuleCat.epi_iff_surjective _).1 hT.epi_g)

/-- `Mod^fg_A` is an abelian category when `A` is Noetherian. -/
public instance instAbelianFiniteGradedModules :
    Abelian (FiniteGradedModules.{u, v, w} 𝒮) := inferInstance

/-! ### `M ↦ M̃` restricted to `Mod^fg_A` -/

/-- The restriction of `M ↦ M̃` to the finitely generated graded modules. -/
public def finiteAssociatedSheafFunctor :
    FiniteGradedModules.{u, u, w} 𝒮 ⥤
      SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  ObjectProperty.ι (C := GradedModuleCat.{u, u, w} 𝒮) (fun M => Module.Finite S M.carrier) ⋙
    associatedModuleSheafFunctor 𝒮

/-- The restriction of `M ↦ M̃` to `Mod^fg_A` is additive. -/
public instance : (finiteAssociatedSheafFunctor.{u, w} 𝒮).Additive :=
  inferInstanceAs
    ((ObjectProperty.ι (C := GradedModuleCat.{u, u, w} 𝒮)
      (fun M => Module.Finite S M.carrier) ⋙ associatedModuleSheafFunctor 𝒮).Additive)

/-- The restriction of `M ↦ M̃` to `Mod^fg_A` preserves finite limits. -/
public theorem preservesFiniteLimits_finiteAssociatedSheafFunctor :
    PreservesFiniteLimits (finiteAssociatedSheafFunctor.{u, w} 𝒮) :=
  have := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass
    (C := GradedModuleCat.{u, u, w} 𝒮) (fun M => Module.Finite S M.carrier)
  have := preservesFiniteLimits_associatedModuleSheafFunctor.{u, w} 𝒮
  inferInstanceAs (PreservesFiniteLimits
    (ObjectProperty.ι (C := GradedModuleCat.{u, u, w} 𝒮)
      (fun M => Module.Finite S M.carrier) ⋙ associatedModuleSheafFunctor 𝒮))

/-- The restriction of `M ↦ M̃` to `Mod^fg_A` preserves finite colimits. -/
public theorem preservesFiniteColimits_finiteAssociatedSheafFunctor :
    PreservesFiniteColimits (finiteAssociatedSheafFunctor.{u, w} 𝒮) :=
  have := ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass
    (C := GradedModuleCat.{u, u, w} 𝒮) (fun M => Module.Finite S M.carrier)
  have := preservesFiniteColimits_associatedModuleSheafFunctor.{u, w} 𝒮
  inferInstanceAs (PreservesFiniteColimits
    (ObjectProperty.ι (C := GradedModuleCat.{u, u, w} 𝒮)
      (fun M => Module.Finite S M.carrier) ⋙ associatedModuleSheafFunctor 𝒮))

/-- A monomorphism of finitely generated graded modules is injective on carriers. -/
public theorem injective_of_mono_finite {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y)
    [Mono f] : Function.Injective f.hom.toLinearMap := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have h₂ := congrArg (fun k => k.hom.toLinearMap ⟨x, hx⟩)
    ((cancel_mono f).1 ((finiteKerι_comp 𝒮 f).trans zero_comp.symm))
  simp only [finiteKerι, kerι] at h₂
  exact h₂

/-- An epimorphism of finitely generated graded modules is surjective on carriers. -/
public theorem surjective_of_epi_finite {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y)
    [Epi f] : Function.Surjective f.hom.toLinearMap := by
  have := Y.property
  let C : FiniteGradedModules.{u, v, w} 𝒮 :=
    ⟨cokerObj f.hom, Module.Finite.of_surjective
      (LinearMap.range f.hom.toLinearMap).mkQ (Submodule.mkQ_surjective _)⟩
  have hz : f ≫ (⟨cokerπ f.hom⟩ : Y ⟶ C) = f ≫ (⟨0⟩ : Y ⟶ C) := by
    ext
    simpa using comp_cokerπ f.hom
  intro n
  have h₂ : (cokerπ f.hom).toLinearMap n = 0 :=
    congrArg (fun k : Y ⟶ C => k.hom.toLinearMap n) ((cancel_epi f).1 hz)
  exact (Submodule.Quotient.mk_eq_zero _).1 h₂

/-- In a short exact sequence of finitely generated graded modules, every element of the middle
term killed by the second map comes from the first. -/
public theorem exists_preimage_of_shortExact_finite
    {T : ShortComplex (FiniteGradedModules.{u, v, w} 𝒮)} (hT : T.ShortExact)
    (y : T.X₂.obj.carrier) (hy : T.g.hom.toLinearMap y = 0) :
    ∃ x, T.f.hom.toLinearMap x = y := by
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hT.fIsKernel (finiteKerι 𝒮 T.g) (finiteKerι_comp 𝒮 T.g)
  exact ⟨l.hom.toLinearMap ⟨y, hy⟩, congrArg (fun k => k.hom.toLinearMap ⟨y, hy⟩) hl⟩

end Finite

/-! ### Irrelevance passes to subobjects and quotients -/

variable {d : ℕ}

/-- Irrelevance passes to a graded submodule. -/
public theorem isIrrelevant_of_injective {L N : GradedModuleCat.{u, v, w} 𝒮} (f : L ⟶ N)
    (hinj : Function.Injective f.toLinearMap) (hN : IsIrrelevant 𝒮 d N) :
    IsIrrelevant 𝒮 d L := by
  intro i x hx
  obtain ⟨N₀, hN₀⟩ := hN i (f.toLinearMap x) (f.map_grade i x hx)
  refine ⟨N₀, fun n hn k hk hki a ha => hinj ?_⟩
  rw [map_zero, map_smul]
  exact hN₀ n hn k hk hki a ha

/-- Irrelevance passes to a graded quotient. -/
public theorem isIrrelevant_of_surjective {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N)
    (hsurj : Function.Surjective f.toLinearMap) (hM : IsIrrelevant 𝒮 d M) :
    IsIrrelevant 𝒮 d N := by
  intro i y hy
  obtain ⟨x, rfl⟩ := hsurj y
  have hd := Stacks.GradedModule.decompose_apply_map (ℳ := M.grade) (𝒩 := N.grade)
    f.toLinearMap.toAddMonoidHom (fun j z hz => f.map_grade j z hz) x i
  have hfx : f.toLinearMap ((DirectSum.decompose M.grade x i : M.carrier)) =
      f.toLinearMap x := hd.symm.trans (DirectSum.decompose_of_mem_same N.grade hy)
  obtain ⟨N₀, hN₀⟩ := hM i _ (DirectSum.decompose M.grade x i).2
  refine ⟨N₀, fun n hn k hk hki a ha => ?_⟩
  rw [← hfx, ← map_smul, hN₀ n hn k hk hki a ha, map_zero]

/-! ### The irrelevant modules are a Serre class -/

section Serre

variable [IsNoetherianRing S]

/-- The irrelevant finitely generated graded modules (Tag 0BXE) are a Serre class in `Mod^fg_A`:
the subcategory contains a zero object and is closed under subobjects, quotients and
extensions. -/
@[stacks 0BXF "the Serre-subcategory step of the proposition: the irrelevant finitely \
generated graded modules are a Serre class in Mod^fg_A, which is what makes the quotient \
category on the left of the arrow exist, and which this file turns into that quotient \
category. The equivalence with Coh(O_X) and the identification of its quasi-inverse with \
F ↦ ⨁_{n ≥ 0} Γ(X, F(n)) are exists_coherentIrrelevantQuotientEquivalence of \
CoherentEquivalence.lean"]
public theorem isSerreClass_irrelevantModules (hd : 0 < d) :
    ObjectProperty.IsSerreClass (irrelevantModules.{u, v, w} 𝒮 d) where
  exists_zero := by
    have hs : Subsingleton (zeroObj.{u, v, w} (𝒮 := 𝒮)).carrier :=
      inferInstanceAs (Subsingleton PUnit.{v + 1})
    have hfin : Module.Finite S (zeroObj.{u, v, w} (𝒮 := 𝒮)).carrier :=
      ⟨⟨∅, eq_top_iff.2 fun x _ => by
        rw [show x = 0 from hs.elim _ _]; exact Submodule.zero_mem _⟩⟩
    refine ⟨⟨zeroObj, hfin⟩, ⟨fun Y => ⟨⟨⟨⟨0⟩⟩, fun f => ?_⟩⟩,
      fun Y => ⟨⟨⟨⟨0⟩⟩, fun f => ?_⟩⟩⟩, isIrrelevant_of_subsingleton 𝒮⟩
    · ext
      exact isZero_zeroObj.eq_of_src _ _
    · ext
      exact isZero_zeroObj.eq_of_tgt _ _
  prop_of_mono {X Y} f hmono hY :=
    isIrrelevant_of_injective 𝒮 f.hom (injective_of_mono_finite 𝒮 f) hY
  prop_of_epi {X Y} f hepi hX :=
    isIrrelevant_of_surjective 𝒮 f.hom (surjective_of_epi_finite 𝒮 f) hX
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have : Module.Finite S T.X₁.obj.carrier := T.X₁.property
    have : Module.Finite S T.X₃.obj.carrier := T.X₃.property
    exact isIrrelevant_of_exact 𝒮 hd T.f.hom T.g.hom
      (fun y hy => exists_preimage_of_shortExact_finite 𝒮 hT y hy) h₁ h₃

end Serre

/-! ### The quotient category -/

section Quotient

variable [IsNoetherianRing S]

/-- The quotient category `Mod^fg_A / Mod^fg_{A, irrelevant}` of Tag 0BXF: the localization of
the finitely generated graded `A`-modules at the morphisms which are isomorphisms modulo the
irrelevant ones. -/
public def IrrelevantQuotient (hd : 0 < d) : Type _ :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)).Localization

/-- The category structure of `IrrelevantQuotient`, that of the localization. -/
public instance (hd : 0 < d) : Category (IrrelevantQuotient 𝒮 hd) :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  inferInstanceAs
    (Category (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)).Localization)

/-- The quotient functor `Mod^fg_A ⟶ Mod^fg_A / Mod^fg_{A, irrelevant}`. -/
public def toIrrelevantQuotient (hd : 0 < d) :
    FiniteGradedModules.{u, v, w} 𝒮 ⥤ IrrelevantQuotient 𝒮 hd :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)).Q

/-- The quotient functor `toIrrelevantQuotient` is a localization at the morphisms which are
isomorphisms modulo the irrelevant modules. -/
public instance (hd : 0 < d) :
    haveI := isSerreClass_irrelevantModules 𝒮 hd
    (toIrrelevantQuotient 𝒮 hd).IsLocalization
      (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)) :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  inferInstanceAs
    ((ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)).Q.IsLocalization _)

/-- The quotient category `Mod^fg_A / Mod^fg_{A, irrelevant}` is preadditive. -/
public instance (hd : 0 < d) : Preadditive (IrrelevantQuotient 𝒮 hd) :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  inferInstanceAs
    (Preadditive (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)).Localization)

/-- The quotient functor is additive. -/
public instance additive_toIrrelevantQuotient (hd : 0 < d) :
    (toIrrelevantQuotient.{u, v, w} 𝒮 hd).Additive :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  Localization.functor_additive (toIrrelevantQuotient.{u, v, w} 𝒮 hd)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d))

end Quotient

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
