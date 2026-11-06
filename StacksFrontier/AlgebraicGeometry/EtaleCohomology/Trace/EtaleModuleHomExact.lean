module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleInjectiveSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction

/-!
# `Hom_R(-, I)` on short exact sequences, for sheaves with injective sections

Let `A` be a commutative ring and `R` an `A`-algebra, not necessarily commutative. For an
`R`-module `N` the group `Hom_R(N, P)` is an `A`-module, `A` acting through the centre of `R`;
this gives the functors `Hom_R(N, -)` from sheaves of `R`-modules to sheaves of `A`-modules on the
small étale site (`Stacks.EtaleCohomology.etaleModuleHom` with
`Stacks.EtaleCohomology.centralScalars`), contravariant in `N`.

A short exact sequence `0 → N' → F → N → 0` of `R`-modules gives, for a sheaf `G` all of whose
modules of sections are injective (an injective sheaf, for instance), a short exact sequence of
sheaves `0 → Hom_R(N, G) → Hom_R(F, G) → Hom_R(N', G) → 0`: it is exact on the sections over
every object, `Hom_R(-, G(U))` being exact.

## Main definitions

* `Stacks.EtaleCohomology.centralScalars`: the action of `A` on an `R`-module, as a ring morphism
  `A →+* (End_R N)ᵐᵒᵖ`.
* `Stacks.EtaleCohomology.homFunctorPrecomp`: the transformation `Hom_R(N₂, -) ⟶ Hom_R(N₁, -)`
  induced by `N₁ ⟶ N₂`.

## Main results

* `Stacks.EtaleCohomology.shortExact_homFunctor_of_injective`
* `Stacks.EtaleCohomology.shortExact_etaleModuleHom_of_injective`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R]

/-- Multiplication by a scalar of `A`, central in `R`, as an endomorphism of an `R`-module. -/
def centralSMulHom (N : ModuleCat.{w} R) (a : A) : N ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun x => algebraMap A R a • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_smul, Algebra.commutes] }

/-- `centralSMulHom N a` is multiplication by `algebraMap A R a`. -/
@[simp]
lemma centralSMulHom_apply (N : ModuleCat.{w} R) (a : A) (x : N) :
    (centralSMulHom N a).hom x = algebraMap A R a • x :=
  rfl

/-- **The action of `A` on an `R`-module `N`**, by `R`-linear endomorphisms. -/
def centralScalars (N : ModuleCat.{w} R) : A →+* (End N)ᵐᵒᵖ where
  toFun a := MulOpposite.op (End.of (centralSMulHom N a))
  map_one' := by
    apply MulOpposite.unop_injective
    apply End.ext
    change centralSMulHom N 1 = (𝟙 N : N ⟶ N)
    ext x
    simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    apply End.ext
    change centralSMulHom N (a * b) = centralSMulHom N a ≫ centralSMulHom N b
    ext x
    change algebraMap A R (a * b) • x = algebraMap A R b • (algebraMap A R a • x)
    rw [smul_smul, ← map_mul, mul_comm]
  map_zero' := by
    apply MulOpposite.unop_injective
    apply End.ext
    change centralSMulHom N 0 = (0 : N ⟶ N)
    ext x
    simp
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply End.ext
    change centralSMulHom N (a + b) = centralSMulHom N a + centralSMulHom N b
    ext x
    change algebraMap A R (a + b) • x = algebraMap A R a • x + algebraMap A R b • x
    rw [map_add, add_smul]

/-- An `R`-linear map commutes with the action of `A`. -/
lemma centralSMulHom_comp {N₁ N₂ : ModuleCat.{w} R} (u : N₁ ⟶ N₂) (a : A) :
    centralSMulHom N₁ a ≫ u = u ≫ centralSMulHom N₂ a := by
  ext x
  simp

/-- **The transformation `Hom_R(N₂, -) ⟶ Hom_R(N₁, -)`** of precomposition with `u : N₁ ⟶ N₂`. -/
def homFunctorPrecomp {N₁ N₂ : ModuleCat.{w} R} (u : N₁ ⟶ N₂) :
    homFunctor N₂ (centralScalars (A := A) N₂) ⟶ homFunctor N₁ (centralScalars N₁) where
  app P := ModuleCat.ofHom (R := A) (X := ↑((homFunctor N₂ (centralScalars (A := A) N₂)).obj P))
    (Y := ↑((homFunctor N₁ (centralScalars (A := A) N₁)).obj P))
    { toFun := fun f => (u ≫ (show N₂ ⟶ P from f) : N₁ ⟶ P)
      map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun a f => by
        change u ≫ (centralSMulHom N₂ a ≫ (show N₂ ⟶ P from f)) =
          centralSMulHom N₁ a ≫ u ≫ (show N₂ ⟶ P from f)
        rw [← Category.assoc, ← centralSMulHom_comp, Category.assoc] }
  naturality P Q g := by
    ext f
    change u ≫ ((show N₂ ⟶ P from f) ≫ g) = (u ≫ (show N₂ ⟶ P from f)) ≫ g
    rw [Category.assoc]

/-- `homFunctorPrecomp u` sends `f : N₂ ⟶ P` to `u ≫ f`. -/
@[simp]
lemma homFunctorPrecomp_app_apply {N₁ N₂ : ModuleCat.{w} R} (u : N₁ ⟶ N₂) (P : ModuleCat.{w} R)
    (f : (homFunctor N₂ (centralScalars (A := A) N₂)).obj P) :
    ((homFunctorPrecomp u).app P).hom f = (u ≫ (show N₂ ⟶ P from f) : N₁ ⟶ P) :=
  rfl

/-- **`Hom_R(-, P)` is exact for `P` injective**: a short exact sequence `0 → N' → F → N → 0`
gives a short exact sequence `0 → Hom_R(N, P) → Hom_R(F, P) → Hom_R(N', P) → 0`. -/
theorem shortExact_homFunctor_of_injective (S : ShortComplex (ModuleCat.{w} R)) (hS : S.ShortExact)
    (P : ModuleCat.{w} R) [Injective P] :
    (ShortComplex.mk ((homFunctorPrecomp (A := A) S.g).app P) ((homFunctorPrecomp S.f).app P) (by
      ext f
      change S.f ≫ S.g ≫ (show S.X₃ ⟶ P from f) = 0
      rw [← Category.assoc, S.zero, zero_comp])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro f hf
    have hf' : S.f ≫ (show S.X₂ ⟶ P from f) = 0 := hf
    exact ⟨hS.gIsCokernel.desc (CokernelCofork.ofπ _ hf'),
      hS.gIsCokernel.fac _ WalkingParallelPair.one⟩
  · rw [ModuleCat.mono_iff_injective]
    intro f g hfg
    exact (cancel_epi S.g).1 hfg
  · rw [ModuleCat.epi_iff_surjective]
    intro h
    exact ⟨Injective.factorThru (show S.X₁ ⟶ P from h) S.f,
      Injective.comp_factorThru (show S.X₁ ⟶ P from h) S.f⟩

/-- **The transformation `Hom_R(N₂, -) ⟶ Hom_R(N₁, -)` of sheaves** induced by `u : N₁ ⟶ N₂`. -/
def etaleModuleHomPrecomp {N₁ N₂ : ModuleCat.{u + 1} R} (u : N₁ ⟶ N₂) (X : Scheme.{u}) :
    etaleModuleHom N₂ (centralScalars (A := A) N₂) X ⟶ etaleModuleHom N₁ (centralScalars N₁) X :=
  sheafCompose_map X.smallEtaleTopology (homFunctorPrecomp u)

/-- On sections over `U`, `etaleModuleHomPrecomp u X` is `homFunctorPrecomp u` at the module of
sections of `G` over `U`. -/
lemma etaleModuleHomPrecomp_app_hom_app {N₁ N₂ : ModuleCat.{u + 1} R} (u : N₁ ⟶ N₂)
    {X : Scheme.{u}} (G : EtaleModules.{u, 0} R X) (U : X.Etaleᵒᵖ) :
    ((etaleModuleHomPrecomp (A := A) u X).app G).hom.app U =
      (homFunctorPrecomp u).app (G.obj.obj U) :=
  rfl

/-- **`Hom_R(-, G)` on a short exact sequence of modules, for a sheaf `G` with injective modules of
sections**: `0 → Hom_R(N, G) → Hom_R(F, G) → Hom_R(N', G) → 0` is a short exact sequence of
sheaves of `A`-modules. -/
theorem shortExact_etaleModuleHom_of_injective (S : ShortComplex (ModuleCat.{u + 1} R))
    (hS : S.ShortExact) {X : Scheme.{u}} (G : EtaleModules.{u, 0} R X)
    (hG : ∀ U : X.Etale, Injective (G.obj.obj (op U))) :
    (ShortComplex.mk ((etaleModuleHomPrecomp (A := A) S.g X).app G)
      ((etaleModuleHomPrecomp S.f X).app G) (by
        apply Sheaf.hom_ext
        ext U f
        change S.f ≫ S.g ≫ (show S.X₃ ⟶ G.obj.obj U from f) = 0
        rw [← Category.assoc, S.zero, zero_comp])).ShortExact := by
  have hU := fun U : X.Etaleᵒᵖ => have := hG U.unop
    shortExact_homFunctor_of_injective (A := A) S hS (G.obj.obj U)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine shortComplex_exact_of_sections _ fun U x hx => ?_
    exact ((ShortComplex.moduleCat_exact_iff _).1 (hU U).exact) x hx
  · refine (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mono_of_mono_map ?_
    exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun U => (hU U).mono_f
  · refine (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).epi_of_epi_map ?_
    exact @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ fun U => (hU U).epi_g

end Stacks.EtaleCohomology
