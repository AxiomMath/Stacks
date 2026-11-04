module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.RingTheory.AdicCompletion.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The completed constant sheaf

Let `J` be a Grothendieck topology on `C`, let `R` be a Noetherian commutative ring and let `I`
be an ideal of `R`. This file constructs the completed constant sheaf
`R̲^∧ = lim (R/Iⁿ)̲` of Tag 093M, together with the canonical map `R̲ ⟶ R̲^∧` and the completed
constant ideal sheaf `I̲^∧ = lim (I/Iⁿ)̲`, and proves that `R̲^∧` is flat over the constant sheaf
of rings `R̲`.

## Main definitions

* `Stacks.ConstantSheaf.adicQuotientSystem`: the inverse system `n ↦ R/Iⁿ` of `R`-modules.
* `Stacks.ConstantSheaf.completedConstantSheaf`: the sheaf `R̲^∧ = lim (R/Iⁿ)̲`.
* `Stacks.ConstantSheaf.completedConstantSheafStructureMap`: the canonical map `R̲ ⟶ R̲^∧`,
  characterised by `completedConstantSheafStructureMap_π` and
  `completedConstantSheafStructureMap_unique`.
* `Stacks.ConstantSheaf.sectionsTowerComparison`: the comparison from the `I`-adic quotient
  tower of `Γ(U, R̲)` to the tower `n ↦ Γ(U, (R/Iⁿ)̲)`.
* `Stacks.ConstantSheaf.completedConstantIdealSheaf`: the sheaf `I̲^∧ = lim (I/Iⁿ)̲`, together
  with the canonical map `completedConstantIdealSheafInclusion : I̲^∧ ⟶ R̲^∧`.
* `Stacks.ConstantSheaf.completedConstantSheafOverConstantRing`: `R̲^∧` read as a sheaf of
  modules over the constant sheaf of rings `R̲`, its underlying sheaf of abelian groups being
  identified with that of `R̲^∧` by
  `Stacks.ConstantSheaf.completedConstantSheafOverConstantRingIso`.

## Main results

* `Stacks.ConstantSheaf.bijective_sectionsTowerComparison_app`: the tower comparison is
  bijective at each level. Surjectivity is Tag 093J and injectivity is Tag 093K.
* `Stacks.ConstantSheaf.completedConstantSheafSectionsIso`: consequently `Γ(U, R̲^∧)` is the
  `I`-adic completion of `Γ(U, R̲)`.
* `Stacks.ConstantSheaf.flat_completedConstantSheaf_sections`: `Γ(U, R̲^∧)` is a flat
  `R`-module, by Tag 093L (flatness of `Γ(U, R̲)`) and flatness of the adic completion of a
  flat module over a Noetherian ring, which is the content of Tag 0912 used by the source.
* `Stacks.ConstantSheaf.isFlat_completedConstantSheaf`: **Stacks 093M**, `R̲^∧` is flat over the
  constant sheaf of rings `R̲`. This is the objectwise statement above fed through Tags 03ES and
  03ET along the bridge of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge`.

## Implementation notes

Both towers are indexed by all of `ℕᵒᵖ`, so they carry a term at `n = 0`. There `R/I⁰` and
`I/I⁰` are zero; Stacks's `I/Iⁿ` is the term at `n ≥ 1`, where `Iⁿ ⊆ I`, and for uniformity
`adicIdealQuotientSystem` divides `I` by the preimage of `Iⁿ` in `I` rather than by `Iⁿ`.

The identification `R̲^∧/I̲^∧ = (R/I)̲` is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletionQuotient`, which also
constructs the map `R̲^∧ ⟶ (R/I)̲` whose cokernel sequence it is. The identification
`R̲^∧/I R̲^∧ = (R/I)̲`, together with the equality `I · R̲^∧ = I̲^∧` of subsheaves of `R̲^∧` it
rests on, is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletionIdealAction`; the
remaining identification of Tag 093M, `R̲^∧/I̲ · R̲^∧ = (R/I)̲`, is not proved anywhere, for the
reason recorded in the implementation notes of that file. The two
identifications `R̲/I R̲ = R̲/I̲ = (R/I)̲` that do not involve `R̲^∧` are in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafQuotient`.

The hypotheses on the site beyond `HasWeakSheafify J (ModuleCat R)` are those of Tags 093J,
093K and 093L, which this file uses unchanged; see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules`.

## References

* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [CommRing R] (I : Ideal R)

/-- The inverse system `n ↦ R/Iⁿ` of `R`-modules, with the canonical quotient maps as
transition maps. -/
noncomputable def adicQuotientSystem : ℕᵒᵖ ⥤ ModuleCat.{w} R where
  obj n := ModuleCat.of R (R ⧸ I ^ n.unop)
  map {i j} hij := ModuleCat.ofHom <|
    (I ^ i.unop).mapQ (I ^ j.unop) LinearMap.id (by
      simpa using Ideal.pow_le_pow_right (leOfHom hij.unop))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp

/-- The cone on `n ↦ R/Iⁿ` with vertex `R`, whose legs are the quotient maps. -/
noncomputable def adicQuotientCone : Cone (adicQuotientSystem I) where
  pt := ModuleCat.of R R
  π :=
    { app := fun n => ModuleCat.ofHom (I ^ n.unop).mkQ
      naturality := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }

variable [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The inverse system `n ↦ (R/Iⁿ)̲` of constant sheaves of `R`-modules. -/
noncomputable abbrev adicQuotientSheafSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  adicQuotientSystem I ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The completed constant sheaf `R̲^∧ = lim (R/Iⁿ)̲`. -/
@[stacks 093M "the completed constant sheaf lim (R/Iⁿ)̲"]
noncomputable def completedConstantSheaf : Sheaf J (ModuleCat.{w} R) :=
  limit (adicQuotientSheafSystem J I)

/-- The projection of the completed constant sheaf onto its `n`-th level `(R/Iⁿ)̲`. -/
noncomputable def completedConstantSheafπ (n : ℕᵒᵖ) :
    completedConstantSheaf J I ⟶ (adicQuotientSheafSystem J I).obj n :=
  limit.π _ n

/-- The cone on the system of constant quotient sheaves whose legs are the constant sheaves of
the ring quotient maps `R ⟶ R/Iⁿ`. -/
noncomputable def constantQuotientCone : Cone (adicQuotientSheafSystem J I) :=
  (constantSheaf J (ModuleCat.{w} R)).mapCone (adicQuotientCone I)

/-- The canonical map `R̲ ⟶ R̲^∧` from the constant sheaf to its completion. -/
@[stacks 093M "the canonical map from the constant sheaf to its completion"]
noncomputable def completedConstantSheafStructureMap :
    (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ completedConstantSheaf J I :=
  limit.lift (adicQuotientSheafSystem J I) (constantQuotientCone J I)

/-- The composite of the canonical map `R̲ ⟶ R̲^∧` with the `n`-th projection is the constant
sheaf of the quotient map `R ⟶ R/Iⁿ`. -/
@[simp]
theorem completedConstantSheafStructureMap_π (n : ℕᵒᵖ) :
    completedConstantSheafStructureMap J I ≫ completedConstantSheafπ J I n =
      (constantSheaf J (ModuleCat.{w} R)).map (ModuleCat.ofHom (I ^ n.unop).mkQ) :=
  limit.lift_π (constantQuotientCone J I) n

/-- The canonical map `R̲ ⟶ R̲^∧` is the unique one compatible with every quotient
projection. -/
theorem completedConstantSheafStructureMap_unique
    (g : (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶
      completedConstantSheaf J I)
    (hg : ∀ n : ℕᵒᵖ, g ≫ completedConstantSheafπ J I n =
      (constantSheaf J (ModuleCat.{w} R)).map (ModuleCat.ofHom (I ^ n.unop).mkQ)) :
    g = completedConstantSheafStructureMap J I := by
  refine limit.hom_ext fun n => ?_
  exact (hg n).trans (completedConstantSheafStructureMap_π J I n).symm

/-- A scalar annihilating a module annihilates the sections of the constant sheaf it
generates: the action of `r` on sections is the functor applied to `r • 𝟙`. -/
theorem smul_constantSections_eq_zero (U : C) (M : ModuleCat.{w} R) (r : R)
    (hr : ∀ m : M, r • m = 0) (y : (constantSections J U).obj M) : r • y = 0 := by
  have h0 : r • (𝟙 M) = 0 := ModuleCat.hom_ext (LinearMap.ext hr)
  have h1 : r • (𝟙 ((constantSections J U).obj M)) = 0 := by
    have e1 : (constantSections J U (R := R)).map (r • 𝟙 M) =
        r • 𝟙 ((constantSections J U).obj M) := by
      rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [← e1, h0, CategoryTheory.Functor.map_zero]
  exact congrArg
    (fun g : (constantSections J U).obj M ⟶ (constantSections J U).obj M => g.hom y) h1

/-- The submodule `Iⁿ · Γ(U, R̲)` is contained in the kernel of the map to the sections of
`(R/Iⁿ)̲`. -/
theorem pow_smul_top_le_ker_constantSections_mkQ (U : C) (n : ℕ) :
    (I ^ n) • (⊤ : Submodule R ((constantSections J U).obj (ModuleCat.of R R))) ≤
      LinearMap.ker ((constantSections J U).map (ModuleCat.ofHom (I ^ n).mkQ)).hom := by
  rw [Submodule.smul_le]
  intro r hr s _
  rw [LinearMap.mem_ker, map_smul]
  refine smul_constantSections_eq_zero J U (ModuleCat.of R (R ⧸ I ^ n)) r (fun m => ?_) _
  induction m using Submodule.Quotient.induction_on with
  | _ a =>
    have hmem : r • a ∈ I ^ n := by
      rw [smul_eq_mul]
      exact Ideal.mul_mem_right a _ hr
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-- The maps `Γ(U, R̲) ⟶ Γ(U, (R/Iⁿ)̲)` are compatible with the transition maps of the
tower of constant quotient sheaves. -/
theorem constantSections_mkQ_comp (U : C) {i j : ℕᵒᵖ} (hij : i ⟶ j) :
    ((constantSections J U).map ((adicQuotientSystem I).map hij)).hom.comp
        ((constantSections J U).map (ModuleCat.ofHom (I ^ i.unop).mkQ)).hom =
      ((constantSections J U).map (ModuleCat.ofHom (I ^ j.unop).mkQ)).hom := by
  have h0 : ModuleCat.ofHom (I ^ i.unop).mkQ ≫ (adicQuotientSystem I).map hij =
      ModuleCat.ofHom (I ^ j.unop).mkQ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rfl
  have h : (constantSections J U).map (ModuleCat.ofHom (I ^ i.unop).mkQ) ≫
      (constantSections J U).map ((adicQuotientSystem I).map hij) =
      (constantSections J U).map (ModuleCat.ofHom (I ^ j.unop).mkQ) :=
    ((constantSections J U (R := R)).map_comp _ _).symm.trans
      (congrArg (fun k => (constantSections J U (R := R)).map k) h0)
  exact congrArg (fun f => ModuleCat.Hom.hom f) h

/-- The comparison from the `I`-adic quotient tower of `Γ(U, R̲)` to the tower of sections of
the constant quotient sheaves `(R/Iⁿ)̲`. -/
noncomputable def sectionsTowerComparison (U : C) :
    quotientTower I ((constantSections J U).obj (ModuleCat.of R R)) ⟶
      adicQuotientSheafSystem J I ⋙ (sheafSections J (ModuleCat.{w} R)).obj (op U) where
  app n := ModuleCat.ofHom (Submodule.liftQ _
    ((constantSections J U).map (ModuleCat.ofHom (I ^ n.unop).mkQ)).hom
    (pow_smul_top_le_ker_constantSections_mkQ J I U n.unop))
  naturality := by
    intro i j hij
    apply ModuleCat.hom_ext
    refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
    exact congrArg (fun f => f a) (constantSections_mkQ_comp J I U hij).symm

/-- At level `n`, the tower comparison sends the class of a section `a` of `R̲` to its image in
the sections of `(R/Iⁿ)̲`. -/
@[simp]
theorem sectionsTowerComparison_app_mk (U : C) (n : ℕᵒᵖ)
    (a : (constantSections J U).obj (ModuleCat.of R R)) :
    ((sectionsTowerComparison J I U).app n).hom (Submodule.Quotient.mk a) =
      ((constantSections J U).map (ModuleCat.ofHom (I ^ n.unop).mkQ)).hom a :=
  rfl

section IdealCompletion

/-- The inverse system `n ↦ I/Iⁿ` of `R`-modules, with `I/Iⁿ` realised as the quotient of the
module `I` by the preimage of `Iⁿ` under the inclusion `I ⟶ R`; for `n ≥ 1`, where `Iⁿ ⊆ I`,
this preimage is `Iⁿ` itself. The transition maps are the canonical quotient maps. -/
noncomputable def adicIdealQuotientSystem : ℕᵒᵖ ⥤ ModuleCat.{w} R where
  obj n := ModuleCat.of R (I ⧸ Submodule.comap I.subtype (I ^ n.unop))
  map {i j} hij := ModuleCat.ofHom <|
    (Submodule.comap I.subtype (I ^ i.unop)).mapQ _ LinearMap.id
      (Submodule.comap_mono (Ideal.pow_le_pow_right (leOfHom hij.unop)))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp

/-- The inclusions `I/Iⁿ ⟶ R/Iⁿ` of inverse systems of `R`-modules. -/
noncomputable def adicIdealQuotientInclusion :
    adicIdealQuotientSystem I ⟶ adicQuotientSystem I where
  app n := ModuleCat.ofHom <|
    (Submodule.comap I.subtype (I ^ n.unop)).mapQ (I ^ n.unop) I.subtype le_rfl
  naturality := by
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    rfl

/-- The inverse system `n ↦ (I/Iⁿ)̲` of constant sheaves of `R`-modules. -/
noncomputable abbrev adicIdealQuotientSheafSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  adicIdealQuotientSystem I ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The completed constant ideal sheaf `I̲^∧ = lim (I/Iⁿ)̲`. -/
@[stacks 093M "the completed ideal sheaf I̲^∧ = lim (I/Iⁿ)̲"]
noncomputable def completedConstantIdealSheaf : Sheaf J (ModuleCat.{w} R) :=
  limit (adicIdealQuotientSheafSystem J I)

/-- The projection of the completed constant ideal sheaf onto its `n`-th level `(I/Iⁿ)̲`. -/
noncomputable def completedConstantIdealSheafπ (n : ℕᵒᵖ) :
    completedConstantIdealSheaf J I ⟶ (adicIdealQuotientSheafSystem J I).obj n :=
  limit.π _ n

/-- The canonical map `I̲^∧ ⟶ R̲^∧`, the limit of the inclusions `(I/Iⁿ)̲ ⟶ (R/Iⁿ)̲`. -/
noncomputable def completedConstantIdealSheafInclusion :
    completedConstantIdealSheaf J I ⟶ completedConstantSheaf J I :=
  limMap (Functor.whiskerRight (adicIdealQuotientInclusion I) (constantSheaf J (ModuleCat.{w} R)))

/-- The canonical map `I̲^∧ ⟶ R̲^∧` followed by the `n`-th projection equals the `n`-th
projection followed by the inclusion `(I/Iⁿ)̲ ⟶ (R/Iⁿ)̲`. -/
@[simp]
theorem completedConstantIdealSheafInclusion_π (n : ℕᵒᵖ) :
    completedConstantIdealSheafInclusion J I ≫ completedConstantSheafπ J I n =
      completedConstantIdealSheafπ J I n ≫
        (constantSheaf J (ModuleCat.{w} R)).map ((adicIdealQuotientInclusion I).app n) :=
  limMap_π _ n

end IdealCompletion

section Flat

variable [IsNoetherianRing R] [HasSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]

/-- The kernel of `Γ(U, R̲) ⟶ Γ(U, (R/Iⁿ)̲)` is contained in `Iⁿ · Γ(U, R̲)`. -/
theorem ker_constantSections_mkQ_le_pow_smul_top (U : C) (n : ℕ) :
    LinearMap.ker ((constantSections J U).map (ModuleCat.ofHom (I ^ n).mkQ)).hom ≤
      (I ^ n) • (⊤ : Submodule R ((constantSections J U).obj (ModuleCat.of R R))) := by
  have hfin : Module.Finite R (R ⧸ I ^ n) :=
    Module.Finite.of_surjective (I ^ n).mkQ (Submodule.mkQ_surjective _)
  have hfp : Module.FinitePresentation R (R ⧸ I ^ n) :=
    Module.finitePresentation_of_finite R _
  have hmap : ModuleCat.ofHom ((TensorProduct.lid R (R ⧸ I ^ n)).toLinearMap ∘ₗ
      (TensorProduct.mk R (ModuleCat.of R R) (ModuleCat.of R (R ⧸ I ^ n))).flip
        (1 : R ⧸ I ^ n)) = ModuleCat.ofHom (I ^ n).mkQ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    show (TensorProduct.lid R (R ⧸ I ^ n)) (r ⊗ₜ[R] (1 : R ⧸ I ^ n)) = (I ^ n).mkQ r
    rw [TensorProduct.lid_tmul, Submodule.mkQ_apply,
      show r • (1 : R ⧸ I ^ n) = Submodule.Quotient.mk (r • (1 : R)) from rfl, smul_eq_mul,
      mul_one]
  intro s hs
  have h0 : (tensorComparison J (ModuleCat.of R R) (ModuleCat.of R (R ⧸ I ^ n))
      (ModuleCat.of R (R ⧸ I ^ n)) (TensorProduct.lid R (R ⧸ I ^ n)) U).1
        (s ⊗ₜ[R] (1 : R ⧸ I ^ n)) = 0 := by
    rw [(tensorComparison J (ModuleCat.of R R) (ModuleCat.of R (R ⧸ I ^ n))
      (ModuleCat.of R (R ⧸ I ^ n)) (TensorProduct.lid R (R ⧸ I ^ n)) U).2 s 1, hmap]
    exact hs
  have h1 : s ⊗ₜ[R] (1 : R ⧸ I ^ n) = 0 :=
    (bijective_tensorComparison J (ModuleCat.of R R) (ModuleCat.of R (R ⧸ I ^ n))
      (ModuleCat.of R (R ⧸ I ^ n)) (TensorProduct.lid R (R ⧸ I ^ n)) U).injective
      (h0.trans (map_zero _).symm)
  have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul
    ((constantSections J U).obj (ModuleCat.of R R)) (I ^ n)) h1
  rw [map_zero, show (1 : R ⧸ I ^ n) = Ideal.Quotient.mk (I ^ n) 1 from (map_one _).symm,
    TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul] at h2
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

/-- Every level of the tower comparison is bijective. -/
theorem bijective_sectionsTowerComparison_app (U : C) (n : ℕᵒᵖ) :
    Function.Bijective ((sectionsTowerComparison J I U).app n).hom := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      exact (Submodule.Quotient.mk_eq_zero _).2
        (ker_constantSections_mkQ_le_pow_smul_top J I U n.unop hx)
  · intro y
    obtain ⟨a, ha⟩ := surjective_constantSections_map J (ModuleCat.ofHom (I ^ n.unop).mkQ)
      (Submodule.mkQ_surjective _) U y
    exact ⟨Submodule.Quotient.mk a, by rw [sectionsTowerComparison_app_mk]; exact ha⟩

/-- The comparison from the `I`-adic quotient tower of `Γ(U, R̲)` to the tower of sections of
the constant quotient sheaves `(R/Iⁿ)̲` is an isomorphism. -/
instance isIso_sectionsTowerComparison (U : C) : IsIso (sectionsTowerComparison J I U) := by
  have : ∀ n : ℕᵒᵖ, IsIso ((sectionsTowerComparison J I U).app n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_sectionsTowerComparison_app J I U n)
  exact NatIso.isIso_of_isIso_app _

/-- The sections of the completed constant sheaf over an object `U`, identified with the
`I`-adic completion of the sections of the constant sheaf `R̲` over `U`. -/
noncomputable def completedConstantSheafSectionsIso (U : C) :
    ((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj (completedConstantSheaf J I) ≅
      ModuleCat.of R
        (AdicCompletion I ((constantSections J U).obj (ModuleCat.of R R))) := by
  have hev : PreservesLimitsOfShape ℕᵒᵖ
      ((sheafSections J (ModuleCat.{w} R)).obj (op U)) :=
    preservesLimitsOfShape_of_natIso
      (sheafSectionsNatIsoEvaluation (J := J) (A := ModuleCat.{w} R) (X := U)).symm
  refine preservesLimitIso ((sheafSections J (ModuleCat.{w} R)).obj (op U))
    (adicQuotientSheafSystem J I) ≪≫
      (HasLimit.isoOfNatIso (asIso (sectionsTowerComparison J I U))).symm ≪≫ ?_
  exact (limit.isLimit _).conePointUniqueUpToIso
    (adicCompletionIsLimit I ((constantSections J U).obj (ModuleCat.of R R)))

/-- On every object of the site the sections of the completed constant sheaf form a flat
`R`-module. -/
@[stacks 093M "Γ(U, R̲^∧) is a flat R-module for every U, the first step of the flatness proof"]
theorem flat_completedConstantSheaf_sections (U : C) :
    Module.Flat R
      (((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj (completedConstantSheaf J I)) := by
  have hcoh : IsCoherentRing R := isCoherentRing_of_isNoetherianRing R
  have hflat : Module.Flat R
      (AdicCompletion I ((constantSections J U).obj (ModuleCat.of R R))) :=
    adicCompletion_flat_of_flat I _
  exact Module.Flat.of_linearEquiv (completedConstantSheafSectionsIso J I U).toLinearEquiv

section SheafFlat

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- The completed constant sheaf, read as a sheaf of modules over the constant sheaf of rings
`R̲`. Its underlying sheaf of abelian groups is that of `R̲^∧`, by
`completedConstantSheafOverConstantRingIso`. -/
noncomputable abbrev completedConstantSheafOverConstantRing :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantRingSheaf J R)) :=
  sheafOfModulesOfConstantRing J (constantRingSheafMap J R) (completedConstantSheaf J I)

/-- Reading `R̲^∧` as a sheaf of modules over the constant sheaf of rings does not change it:
the underlying sheaf of abelian groups is still that of `R̲^∧`. -/
noncomputable def completedConstantSheafOverConstantRingIso
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})] :
    (SheafOfModules.toSheaf _).obj (completedConstantSheafOverConstantRing J I) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj
        (completedConstantSheaf J I) :=
  sheafOfModulesOfConstantRingIso J (constantRingSheafMap J R) (completedConstantSheaf J I)

/-- The completed constant sheaf `R̲^∧ = lim (R/Iⁿ)̲` is flat over the constant
sheaf of rings `R̲`. By Tags 03ES and 03ET this follows from the objectwise flatness of
`flat_completedConstantSheaf_sections`. -/
@[stacks 093M "R̲^∧ is flat over R̲"]
theorem isFlat_completedConstantSheaf :
    AlgebraicGeometry.SheafOfModules.IsFlat (completedConstantSheafOverConstantRing J I) :=
  isFlat_sheafOfModulesOfConstantRing J (constantRingSheafMap J R) (completedConstantSheaf J I)
    fun U => flat_completedConstantSheaf_sections J I U.unop

end SheafFlat

end Flat

end Stacks.ConstantSheaf

end
