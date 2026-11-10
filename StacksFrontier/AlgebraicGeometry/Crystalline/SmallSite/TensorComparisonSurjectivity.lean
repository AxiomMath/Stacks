module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ComparisonSurjectivity

/-!
# Hypothesis (2) of [Stacks, Tag 07JN] passes to a tensor product

Work in a global crystalline situation `(p, (S, I, γ), X)`.  Hypothesis (2) of
[Stacks, Tag 07JN] on a presheaf of `𝒪_{X/S}`-modules `F` on the small crystalline site
`Cris(X/S)` is that for every morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` whose map on
ambient schemes is a closed immersion the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is locally
surjective; this is
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.IsSurjectiveComparison`.

This file proves that the condition is stable under the objectwise tensor product: if `F` and
`G` both satisfy it then so does `F ⊗_{𝒪_{X/S}} G`.  It also proves that `Ω_{X/S}` satisfies it,
and deduces the condition for `F ⊗_{𝒪_{X/S}} Ω_{X/S}` from the condition for `F`.

## Main results

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`, the
first four items in its subnamespace `CohomologyRestriction`.

* `CohomologyRestriction.exists_common_open_fmapGenerators`: two generators of the images of the
  comparison morphisms of two presheaves of modules, over the same open of `T`, can be written
  with the same open of `T'` and the same restriction morphism.
* `CohomologyRestriction.tmul_mem_fmapSubmodule_tensorModules`: a pure tensor of a section in the
  image of `c_f` for `F` with a section in the image of `c_f` for `G` is in the image of `c_f` for
  `F ⊗ G`, over every open of `T`.
* `CohomologyRestriction.isSurjectiveComparison_tensorModules`: hypothesis (2) of
  [Stacks, Tag 07JN] for `F ⊗ G`, from hypothesis (2) for `F` and for `G`.
* `CohomologyRestriction.isSurjectiveComparison_crysDifferentials`: [Stacks, Tag 07KM] part (2)
  on the small crystalline site, that is, hypothesis (2) of [Stacks, Tag 07JN] for `Ω_{X/S}`.
* `isSurjectiveComparison_tensorDifferentialForms`: hypothesis (2) for the presheaf
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of `...SmallSite.tensorDifferentialForms`, from hypothesis (2) for `F`
  and for `Ω^i_{X/S}`.
* `isSurjectiveComparison_tensorCrysDifferentials`: hypothesis (2) for `F ⊗_{𝒪_{X/S}} Ω_{X/S}`,
  from hypothesis (2) for `F`.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- The objectwise tensor product of two presheaves of `𝒪_{X/S}`-modules on the small crystalline
site. -/
abbrev tensorModules
    (M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  M ⊗ N

namespace CohomologyRestriction

variable (M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- The sections of a tensor product of presheaves of `𝒪_{X/S}`-modules over the restriction of
an object to an open of its ambient scheme, as a module over the restriction of the structure
presheaf. -/
instance tensorModulesRestrictionModule (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Module ((ringRestriction A).obj V)
      ((tensorModules M N).obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V)) :=
  inferInstanceAs (Module ((ringRestriction A).obj V)
    ((moduleRestriction (tensorModules M N) A).obj V))

/-- The sections of a tensor product over the restriction of an object, read as a bare tensor
product of modules, as a module over the restriction of the structure presheaf. -/
instance tensorProductRestrictionModule (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Module ((ringRestriction A).obj V)
      (TensorProduct ((structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj
          ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
        (M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
        (N.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))) :=
  inferInstanceAs (Module ((ringRestriction A).obj V)
    ((moduleRestriction (tensorModules M N) A).obj V))

/-- A generator of the image of the `f`-map can be rewritten over a smaller object, whenever
the two restriction morphisms compose to the given one: the value of `ψ` over `X` restricted along
`h'` is the value of `ψ` over `X'` at the restricted section, restricted along `h`. -/
theorem map_app_eq_map_app_map {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {R' : Cᵒᵖ ⥤ RingCat.{u}} (φ : R' ⟶ F.op ⋙ R)
    {P : PresheafOfModules.{u} R'} {Q : PresheafOfModules.{u} R}
    (ψ : P ⟶ (PresheafOfModules.pushforward φ).obj Q)
    {X X' : Cᵒᵖ} (t : X ⟶ X') {Y : Dᵒᵖ} (h : op (F.obj X'.unop) ⟶ Y)
    (h' : op (F.obj X.unop) ⟶ Y) (hcomp : F.op.map t ≫ h = h') (s : P.obj X) :
    Q.map h' (ψ.app X s) = Q.map h (ψ.app X' (P.map t s)) := by
  subst hcomp
  exact (PresheafOfModules.map_comp_apply Q (F.op.map t) h (ψ.app X s)).trans
    (congrArg (fun w ↦ Q.map h w) (PresheafOfModules.naturality_apply ψ t s)).symm

end CohomologyRestriction

/-- A pure tensor of two elements of two spans lies in any submodule containing the pure tensors
of the two spanning sets. -/
private theorem tmul_mem_of_mem_span {R : Type u} [CommRing R] {X Y : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (sX : Set X) (sY : Set Y) (T : Submodule R (TensorProduct R X Y))
    (hT : ∀ a ∈ sX, ∀ b ∈ sY, a ⊗ₜ[R] b ∈ T) {x : X} {y : Y}
    (hx : x ∈ Submodule.span R sX) (hy : y ∈ Submodule.span R sY) :
    x ⊗ₜ[R] y ∈ T := by
  have h := Submodule.apply_mem_map₂ (TensorProduct.mk R X Y) hx hy
  rw [Submodule.map₂_span_span] at h
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact hT a ha b hb

namespace CohomologyRestriction

variable (M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- Two generators of the images of the comparison morphisms of two presheaves of modules, over
the same open `W` of `T`, can be written over a common open of `T'`. -/
theorem exists_common_open_fmapGenerators {V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ}
    {x : (moduleRestriction M A).obj V} {y : (moduleRestriction N A).obj V}
    (hx : x ∈ PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g)
      (moduleFMap M g) V)
    (hy : y ∈ PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g)
      (moduleFMap N g) V) :
    ∃ (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ)
      (h : op ((Opens.map g.hom.targetHom.hom.base).obj W.unop) ⟶ V)
      (s : (moduleRestriction M B).obj W) (t : (moduleRestriction N B).obj W),
      x = (moduleRestriction M A).map h ((moduleFMap M g).app W s) ∧
        y = (moduleRestriction N A).map h ((moduleFMap N g).app W t) := by
  obtain ⟨W₁, h₁, s₁, rfl⟩ := hx
  obtain ⟨W₂, h₂, s₂, rfl⟩ := hy
  exact ⟨op (W₁.unop ⊓ W₂.unop),
    (homOfLE fun z hz ↦ ⟨leOfHom h₁.unop hz, leOfHom h₂.unop hz⟩).op,
    (moduleRestriction M B).map (homOfLE (inf_le_left (a := W₁.unop) (b := W₂.unop))).op s₁,
    (moduleRestriction N B).map (homOfLE (inf_le_right (a := W₁.unop) (b := W₂.unop))).op s₂,
    map_app_eq_map_app_map (restrictionFMap (crisRing S) g) (moduleFMap M g) _ _ h₁
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s₁,
    map_app_eq_map_app_map (restrictionFMap (crisRing S) g) (moduleFMap N g) _ _ h₂
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s₂⟩

/-- A pure tensor of a section in the image of `c_f` for `F` with a section in the image of
`c_f` for `G` is in the image of `c_f` for `F ⊗ G`, over every open of the ambient scheme of the
source. -/
theorem tmul_mem_fmapSubmodule_tensorModules {V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ}
    {x : (moduleRestriction M A).obj V} {y : (moduleRestriction N A).obj V}
    (hx : x ∈ (fmapSubmodule M g).obj V) (hy : y ∈ (fmapSubmodule N g).obj V) :
    (x ⊗ₜ y : (moduleRestriction (tensorModules M N) A).obj V) ∈
      (fmapSubmodule (tensorModules M N) g).obj V := by
  refine tmul_mem_of_mem_span
    (R := (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj
      ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
    (X := M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
    (Y := N.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
    (PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g) (moduleFMap M g) V)
    (PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g) (moduleFMap N g) V)
    ((fmapSubmodule (tensorModules M N) g).obj V) ?_ hx hy
  intro a ha b hb
  obtain ⟨W, h, s, t, rfl, rfl⟩ := exists_common_open_fmapGenerators M N g ha hb
  exact (fmapSubmodule (tensorModules M N) g).map_mem h
    (PresheafOfModules.appₛₗ_mem_generatedSubmodule (restrictionFMap (crisRing S) g)
      (moduleFMap (tensorModules M N) g) W (s ⊗ₜ t))

/-- Hypothesis (2) of [Stacks, Tag 07JN] passes to an objectwise tensor product: if the
comparison morphisms `c_f` of two presheaves of `𝒪_{X/S}`-modules on `Cris(X/S)` are locally
surjective along every morphism whose map on ambient schemes is a closed immersion, then so are
the comparison morphisms of their tensor product. -/
theorem isSurjectiveComparison_tensorModules (hM : IsSurjectiveComparison M)
    (hN : IsSurjectiveComparison N) : IsSurjectiveComparison (tensorModules M N) := by
  intro A B g hg
  have := hM g hg
  have := hN g hg
  refine ⟨fun {V} z ↦ ?_⟩
  set J := Opens.grothendieckTopology A.obj.thickening.target.scheme
  set cM := (PresheafOfModules.toPresheaf (ringRestriction A)).map (moduleComparison M g)
  set cN := (PresheafOfModules.toPresheaf (ringRestriction A)).map (moduleComparison N g)
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
      refine J.superset_covering ?_ (J.intersection_covering
        (Presheaf.imageSieve_mem J cM m) (Presheaf.imageSieve_mem J cN n))
      rintro V' i ⟨⟨tm, htm⟩, ⟨tn, htn⟩⟩
      exact (range_moduleComparison_app_eq_fmapSubmodule (tensorModules M N) g (op V')).ge
        (tmul_mem_fmapSubmodule_tensorModules M N g
          ((range_moduleComparison_app_eq_fmapSubmodule M g (op V')).le ⟨tm, htm⟩)
          ((range_moduleComparison_app_eq_fmapSubmodule N g (op V')).le ⟨tn, htn⟩))
  | add z₁ z₂ ih₁ ih₂ =>
      refine J.superset_covering ?_ (J.intersection_covering ih₁ ih₂)
      rintro V' i ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩
      exact ⟨t₁ + t₂, (map_add _ t₁ t₂).trans
        ((congrArg₂ (· + ·) ht₁ ht₂).trans (map_add _ z₁ z₂).symm)⟩

/-- [Stacks, Tag 07KM] part (2) on the small crystalline site: the comparison morphism
`c_f : f^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` of the small-site module of crystalline differentials is
locally surjective along every morphism of `Cris(X/S)` whose map on ambient schemes is a closed
immersion.  That is, `Ω_{X/S}` satisfies hypothesis (2) of [Stacks, Tag 07JN]. -/
theorem isSurjectiveComparison_crysDifferentials :
    IsSurjectiveComparison (crysDifferentials S) := fun g hg ↦
  have := hg
  GlobalCrystallineSituation.isLocallySurjective_moduleComparison S g.hom

end CohomologyRestriction

/-- Hypothesis (2) of [Stacks, Tag 07JN] for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, from hypothesis (2) for
`F` and for `Ω^i_{X/S}`. -/
theorem isSurjectiveComparison_tensorDifferentialForms
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (i : ℕ) (hM : CohomologyRestriction.IsSurjectiveComparison M)
    (hΩ : CohomologyRestriction.IsSurjectiveComparison (crysDifferentialForms S i)) :
    CohomologyRestriction.IsSurjectiveComparison (tensorDifferentialForms M i) :=
  CohomologyRestriction.isSurjectiveComparison_tensorModules M (crysDifferentialForms S i) hM hΩ

/-- Hypothesis (2) of [Stacks, Tag 07JN] for `F ⊗_{𝒪_{X/S}} Ω_{X/S}`, from hypothesis (2) for
`F` alone. -/
theorem isSurjectiveComparison_tensorCrysDifferentials
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hM : CohomologyRestriction.IsSurjectiveComparison M) :
    CohomologyRestriction.IsSurjectiveComparison (tensorModules M (crysDifferentials S)) :=
  CohomologyRestriction.isSurjectiveComparison_tensorModules M (crysDifferentials S) hM
    CohomologyRestriction.isSurjectiveComparison_crysDifferentials

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
