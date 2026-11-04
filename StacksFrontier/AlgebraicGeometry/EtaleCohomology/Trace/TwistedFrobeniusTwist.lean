module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity

/-!
# The Frobenius twist composed with an automorphism

Let `Y` be a scheme over a finite field `k`, `σ : Y ⟶ Y` a morphism over `k` and `k̄` an
algebraically closed extension of `k`. Write `σ̄ = σ × id` and `π̄ = π_Y × id` for the base
changes to `Y_k̄` and `φ = σ̄ ≫ π̄`. A sheaf `C` of `Λ`-modules on `Y_étale` together with a map
`ε : C ⟶ σ_* C` gives a canonical twist

`C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄}) ⟶ π̄_*(σ̄_*(C|_{Y_k̄})) = φ_*(C|_{Y_k̄})`,

the Frobenius base change twist followed by `π̄_*` of the restriction of `ε` (through the base
change map `(σ_* C)|_{Y_k̄} ⟶ σ̄_*(C|_{Y_k̄})`). It is natural in the pair `(C, ε)`, so a short
exact sequence of such pairs is a short exact sequence with a twist, to which the additivity of
`CategoryTheory.Functor.derivedTwistEndo` applies.

For `σ` the action of `g⁻¹` of a Galois group on a curve and `C` the constant sheaf this is the
endomorphism `(g⁻¹ π)^*` of Steps 8 and 9 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `Stacks.EtaleCohomology.twistedGeometricFrobenius`: `φ = σ̄ ≫ π̄`.
* `Stacks.EtaleCohomology.twistedFrobeniusTwist`: the twist `C|_{Y_k̄} ⟶ φ_*(C|_{Y_k̄})`.
* `Stacks.EtaleCohomology.twistedFrobeniusTwistHC`, `twistedFrobeniusTwistComplex`: the same,
  degreewise, for a complex.
* `Stacks.EtaleCohomology.twistedFrobeniusCohomologyEndo`: the endomorphism `φ^*` of
  `RΓ(Y_k̄, K|_{Y_k̄})`.

## Main results

* `Stacks.EtaleCohomology.twistedFrobeniusTwist_naturality`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_twistedFrobeniusCohomologyEndo_X₂_eq_add`: additivity
  of `Tr(φ^*)` along a short exact sequence of complexes with compatible maps `ε`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The twisted geometric Frobenius `φ = σ̄ ≫ π̄` of `Y_k̄`. -/
abbrev twistedGeometricFrobenius : fieldBaseChange Y kbar ⟶ fieldBaseChange Y kbar :=
  fieldBaseChangeMap σ kbar ≫ geometricFrobeniusBaseChange Y kbar p q hcard

/-- `φ` is a morphism over `Spec k̄`. -/
lemma twistedGeometricFrobenius_comp_toBase :
    twistedGeometricFrobenius Y σ kbar p q hcard ≫ pullback.snd Y.hom (specAlgebraMap k kbar) =
      pullback.snd Y.hom (specAlgebraMap k kbar) := by
  rw [Category.assoc, geometricFrobeniusBaseChange_comp_toBase, fieldBaseChangeMap_comp_snd]

/-- The base change map `(σ_* C)|_{Y_k̄} ⟶ σ̄_*(C|_{Y_k̄})`. -/
abbrev automorphismBaseChange :
    etaleModuleDirectImage.{u, r} Λ σ.left ⋙
        etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⟶
      etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap σ kbar) :=
  etaleModuleBaseChange Λ σ.left (fieldBaseChangeMap σ kbar) (fieldBaseChangeProj Y kbar)
    (fieldBaseChangeProj Y kbar) (fieldBaseChangeMap_comp_fst σ kbar)

/-- **The twist `C|_{Y_k̄} ⟶ φ_*(C|_{Y_k̄})`** attached to `ε : C ⟶ σ_* C`: the Frobenius base
change twist, followed by `π̄_*` of the restriction of `ε` and the base change map, and the
composition isomorphism `π̄_* ∘ σ̄_* ≅ φ_*`. -/
def twistedFrobeniusTwist (C : EtaleModules.{u, r} Λ Y.left)
    (ε : C ⟶ (etaleModuleDirectImage.{u, r} Λ σ.left).obj C) :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj C ⟶
      (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj C) :=
  (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app C ≫
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map ε ≫
        (automorphismBaseChange Λ Y σ kbar).app C) ≫
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap σ kbar)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (twistedGeometricFrobenius Y σ kbar p q hcard) rfl).hom.app _

/-- **Naturality of the twisted Frobenius twist** in the pair `(C, ε)`. -/
lemma twistedFrobeniusTwist_naturality {C C' : EtaleModules.{u, r} Λ Y.left}
    (ε : C ⟶ (etaleModuleDirectImage.{u, r} Λ σ.left).obj C)
    (ε' : C' ⟶ (etaleModuleDirectImage.{u, r} Λ σ.left).obj C') (f : C ⟶ C')
    (hf : f ≫ ε' = ε ≫ (etaleModuleDirectImage.{u, r} Λ σ.left).map f) :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map f ≫
        twistedFrobeniusTwist Λ Y σ kbar p q hcard C' ε' =
      twistedFrobeniusTwist Λ Y σ kbar p q hcard C ε ≫
        (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map f) := by
  unfold twistedFrobeniusTwist
  have h1 := (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).naturality f
  have h2 := (automorphismBaseChange Λ Y σ kbar).naturality f
  have h3 := (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap σ kbar)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (twistedGeometricFrobenius Y σ kbar p q hcard) rfl).hom.naturality
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map f)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3
  have key : (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map f ≫
      (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map ε' ≫
        (automorphismBaseChange Λ Y σ kbar).app C' =
      (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map ε ≫
        (automorphismBaseChange Λ Y σ kbar).app C ≫
          (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap σ kbar)).map
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map f) := by
    rw [← Functor.map_comp_assoc, hf, Functor.map_comp, Category.assoc, h2]
  have key' := congrArg (etaleModuleDirectImage.{u, r} Λ
    (geometricFrobeniusBaseChange Y kbar p q hcard)).map key
  simp only [Functor.map_comp] at key'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% key', h3]

/-- **The twisted Frobenius twist of a complex** `K` with a map `ε : K ⟶ σ_* K`, degreewise. -/
def twistedFrobeniusTwistHC (K : CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)
    (ε : K ⟶ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).obj K) :
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
        _).obj K ⟶
      ((etaleModuleDirectImage.{u, r} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex _).obj
        (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) where
  f n := twistedFrobeniusTwist Λ Y σ kbar p q hcard (K.X n) (ε.f n)
  comm' i j _ := (twistedFrobeniusTwist_naturality Λ Y σ kbar p q hcard (ε.f i) (ε.f j) (K.d i j)
    (ε.comm i j).symm).symm

/-- Naturality of `twistedFrobeniusTwistHC` in the pair `(K, ε)`. -/
lemma twistedFrobeniusTwistHC_naturality {K K' : CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ}
    (ε : K ⟶ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).obj K)
    (ε' : K' ⟶ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).obj K')
    (f : K ⟶ K')
    (hf : f ≫ ε' = ε ≫ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).map f) :
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
          _).map f ≫
        twistedFrobeniusTwistHC Λ Y σ kbar p q hcard K' ε' =
      twistedFrobeniusTwistHC Λ Y σ kbar p q hcard K ε ≫
        ((etaleModuleDirectImage.{u, r} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex _).map
          (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
            _).map f) := by
  ext n : 1
  exact twistedFrobeniusTwist_naturality Λ Y σ kbar p q hcard (ε.f n) (ε'.f n) (f.f n)
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n) hf)

/-- The twisted Frobenius twist of a bounded below complex, as a morphism of bounded below
complexes. -/
abbrev twistedFrobeniusTwistComplex (K : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (ε : K.obj ⟶ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).obj K.obj) :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj K ⟶
      (etaleModuleDirectImage.{u, r} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk (twistedFrobeniusTwistHC Λ Y σ kbar p q hcard K.obj ε)

/-- **The endomorphism `φ^*` of `RΓ(Y_k̄, K|_{Y_k̄})`** attached to `ε : K ⟶ σ_* K`, for
`φ = σ̄ ≫ π̄`: the derived endomorphism of the twisted Frobenius twist. For `σ = 𝟙` and `ε` the
identity this is the canonical Frobenius endomorphism. -/
def twistedFrobeniusCohomologyEndo (K : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (ε : K.obj ⟶ ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _).obj K.obj) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar K)) ⟶
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar K)) :=
  Functor.derivedTwistEndo
    (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm)
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj K)
    (twistedFrobeniusTwistComplex Λ Y σ kbar p q hcard K ε)

/-- The twisted Frobenius twist of a short complex of complexes with a compatible `ε`. -/
def twistedFrobeniusTwistShortComplex
    (S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ))
    (ε : S ⟶ S.map ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _)) :
    S.map ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
      (S.map ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomologicalComplex
        (ComplexShape.up ℤ))).map ((etaleModuleDirectImage.{u, r} Λ
          (twistedGeometricFrobenius Y σ kbar p q hcard)).mapHomologicalComplex _) where
  τ₁ := twistedFrobeniusTwistHC Λ Y σ kbar p q hcard S.X₁ ε.τ₁
  τ₂ := twistedFrobeniusTwistHC Λ Y σ kbar p q hcard S.X₂ ε.τ₂
  τ₃ := twistedFrobeniusTwistHC Λ Y σ kbar p q hcard S.X₃ ε.τ₃
  comm₁₂ := (twistedFrobeniusTwistHC_naturality Λ Y σ kbar p q hcard ε.τ₁ ε.τ₂ S.f
    ε.comm₁₂.symm).symm
  comm₂₃ := (twistedFrobeniusTwistHC_naturality Λ Y σ kbar p q hcard ε.τ₂ ε.τ₃ S.g
    ε.comm₂₃.symm).symm

attribute [local instance] HasDerivedCategory.standard in
/-- **Additivity of the trace of `φ^*` along a short exact sequence with a compatible `ε`**:
`Tr(φ^* | RΓ(Y_k̄, X₂)) = Tr(φ^* | RΓ(Y_k̄, X₁)) + Tr(φ^* | RΓ(Y_k̄, X₃))`. -/
theorem perfectDerivedTrace_twistedFrobeniusCohomologyEndo_X₂_eq_add
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)} (hS : S.ShortExact)
    (ε : S ⟶ S.map ((etaleModuleDirectImage.{u, r} Λ σ.left).mapHomologicalComplex _))
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₁, h₁⟩)))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₂, h₂⟩)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar ⟨S.X₃, h₃⟩))))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
        (twistedFrobeniusCohomologyEndo.{u, r} Λ Y σ kbar p q hcard ⟨S.X₂, h₂⟩ ε.τ₂)) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
          (twistedFrobeniusCohomologyEndo.{u, r} Λ Y σ kbar p q hcard ⟨S.X₁, h₁⟩ ε.τ₁)) +
        CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hp₃⟩ (DerivedCategory.Plus.ι.map
          (twistedFrobeniusCohomologyEndo.{u, r} Λ Y σ kbar p q hcard ⟨S.X₃, h₃⟩ ε.τ₃)) :=
  Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add.{r, u + 1}
    (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, r} Λ (twistedGeometricFrobenius Y σ kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard).symm)
    (fieldBaseChangeRestriction_shortExact.{u, r} Λ Y kbar hS)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₁, h₁⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₂, h₂⟩).property)
    (((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ⟨S.X₃, h₃⟩).property)
    (twistedFrobeniusTwistShortComplex Λ Y σ kbar p q hcard S ε) hp₁ hp₂ hp₃

end Stacks.EtaleCohomology
