module

public import StacksFrontier.Algebra.Category.ModuleCat.ExactLinearFunctorFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantGenerators
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.FiniteTypeGlobalGenerators
public import StacksFrontier.CategoryTheory.Sites.SheafModuleCatBiproducts

/-!
# The constant sheaf `\underline{Λ}` on a weakly contractible affine

Let `X` be an affine scheme which is weakly contractible (Stacks 090L) and `Λ` a ring. On the
small pro-étale site `X_proét`, global sections are an exact functor
(`AlgebraicGeometry.Scheme.ProEt.preservesFiniteColimits_sheafSections_mk_id`), and the constant
sheaf functor is left adjoint to global sections. Hence the constant sheaf `\underline{Λ}` is a
projective object of the category of sheaves of `Λ`-modules on `X_proét`, and every sheaf of
`Λ`-modules which is locally constant of finite type is a quotient of a finite direct sum of
copies of `\underline{Λ}`: its finitely many local generators can be chosen global, as in the
first step of the proof of Stacks 09BZ.

## Main results

* `AlgebraicGeometry.ProEtale.projective_constantSheaf_unitModule`: `\underline{Λ}` is
  projective.
* `AlgebraicGeometry.ProEtale.constantSheafHomOfSection_app_constantUnitApp`: the morphism
  `\underline{Λ} ⟶ G` attached to a global section `y` sends the unit section over `W` to the
  restriction of `y`.
* `AlgebraicGeometry.ProEtale.epi_biproductDescOfSections`: global sections which locally span
  give an epimorphism `\underline{Λ}^{⊕ n} ⟶ G`.
* `AlgebraicGeometry.ProEtale.exists_epi_biproduct_constantSheaf_of_isFiniteTypeLocallyConstant`:
  a locally constant sheaf of finite type is a quotient of `\underline{Λ}^{⊕ t}`.

## Implementation notes

`HasFiniteBiproducts` is not found by instance search on sheaves of modules; it is supplied by
the instance `CategoryTheory.Sheaf.hasFiniteBiproducts_moduleCat`, from finite
products as in Mathlib's `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`.

## References

* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ]

/-- **The constant sheaf `\underline{Λ}` is projective on a weakly contractible affine.** Let `X`
be an affine scheme which is weakly contractible. The constant sheaf `\underline{Λ}` is a
projective object of sheaves of `Λ`-modules on `X_proét`: the constant sheaf functor is left
adjoint to global sections, which preserve epimorphisms on `X_proét`, and `Λ` is a projective
`Λ`-module. -/
theorem projective_constantSheaf_unitModule [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X) :
    Projective ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
      (Functor.unitModule Λ)) := by
  have := Scheme.ProEt.preservesFiniteColimits_sheafSections_mk_id hX Λ
  exact (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
    (IsTerminal.ofUniqueHom Scheme.ProEt.toMkId fun _ _ => Scheme.ProEt.hom_ext_mkId _ _)
    ).map_projective _ inferInstance

/-- The morphism `\underline{Λ} ⟶ G` of sheaves of `Λ`-modules on `X_proét` attached to a global
section `y` of `G`, by the constant sheaf adjunction. -/
def constantSheafHomOfSection {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (y : G.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
      (Functor.unitModule Λ) ⟶ G :=
  ((constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
    (IsTerminal.ofUniqueHom Scheme.ProEt.toMkId fun _ _ => Scheme.ProEt.hom_ext_mkId _ _)
    ).homEquiv _ _).symm
      (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ y))

/-- The morphism `\underline{Λ} ⟶ G` attached to a global section `y` sends the canonical unit
section over `W` to the restriction of `y` to `W`. -/
theorem constantSheafHomOfSection_app_constantUnitApp
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (y : G.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) (W : X.ProEt) :
    ((constantSheafHomOfSection y).hom.app (op W)).hom
        ((Stacks.ConstantSheaf.constantUnitApp (Scheme.ProEt.topology X) (Functor.unitModule Λ)
          (op W)).hom (1 : Λ)) =
      (G.obj.map (Scheme.ProEt.toMkId W).op).hom y := by
  let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
    IsTerminal.ofUniqueHom Scheme.ProEt.toMkId fun _ _ => Scheme.ProEt.hom_ext_mkId _ _
  have h1 : (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
      hT).homEquiv _ _ (constantSheafHomOfSection y) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ y) :=
    Equiv.apply_symm_apply _ _
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply] at h1
  have hT1 : ((constantSheafHomOfSection y).hom.app (op (Scheme.ProEt.mk (𝟙 X)))).hom
      ((Stacks.ConstantSheaf.constantUnitApp (Scheme.ProEt.topology X) (Functor.unitModule Λ)
        (op (Scheme.ProEt.mk (𝟙 X)))).hom (1 : Λ)) = y :=
    (ConcreteCategory.congr_hom h1 (1 : Λ)).trans (one_smul Λ y)
  rw [← Stacks.ConstantSheaf.map_constantUnitApp _ _ (Scheme.ProEt.toMkId W).op]
  exact (ConcreteCategory.congr_hom
    ((constantSheafHomOfSection y).hom.naturality (Scheme.ProEt.toMkId W).op) _).trans
      (congrArg (G.obj.map (Scheme.ProEt.toMkId W).op).hom hT1)

/-- The morphism `\underline{Λ}^{⊕ n} ⟶ G` of sheaves of `Λ`-modules on `X_proét` determined by
`n` global sections of `G`. -/
def biproductDescOfSections {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    {n : ℕ} (s : Fin n → G.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))) :
    (⨁ fun _ : Fin n => (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)).obj (Functor.unitModule Λ)) ⟶ G :=
  biproduct.desc fun i => constantSheafHomOfSection (s i)

/-- **Global sections which locally span give an epimorphism from `\underline{Λ}^{⊕ n}`.** Let
`s` be finitely many global sections of a sheaf of `Λ`-modules `G` on `X_proét` such that every
section of `G` is, on a covering sieve, a `Λ`-linear combination of the restrictions of the
`s i`. Then the morphism `\underline{Λ}^{⊕ n} ⟶ G` they determine is an epimorphism. -/
theorem epi_biproductDescOfSections
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    {n : ℕ} (s : Fin n → G.obj.obj (op (Scheme.ProEt.mk (𝟙 X))))
    (hs : ∀ (V : X.ProEt) (m : G.obj.obj (op V)), ∃ S ∈ Scheme.ProEt.topology X V,
      ∀ ⦃W : X.ProEt⦄ (g : W ⟶ V), S g → (G.obj.map g.op).hom m ∈
        Submodule.span Λ (Set.range fun i => (G.obj.map (Scheme.ProEt.toMkId W).op).hom (s i))) :
    Epi (biproductDescOfSections s) := by
  refine (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max (u + 1) w} Λ)
    (biproductDescOfSections s)).1 ⟨fun {V} m => ?_⟩
  obtain ⟨S, hS, h⟩ := hs V m
  refine (Scheme.ProEt.topology X).superset_covering (fun W g hg => ?_) hS
  have hle : Submodule.span Λ (Set.range fun i =>
      (G.obj.map (Scheme.ProEt.toMkId W).op).hom (s i)) ≤
      LinearMap.range ((biproductDescOfSections s).hom.app (op W)).hom := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := constantSheafHomOfSection_app_constantUnitApp (s i) W
    rw [← biproduct.ι_desc (fun i => constantSheafHomOfSection (s i)) i] at this
    exact ⟨_, this⟩
  exact hle (h g hg)

/-- **A locally constant sheaf of finite type on a weakly contractible affine is a quotient of
`\underline{Λ}^{⊕ t}`.** Let `X` be an affine scheme which is weakly contractible and `G` a sheaf
of `Λ`-modules on `X_proét` which is locally constant of finite type. There are an integer `t`
and an epimorphism `\underline{Λ}^{⊕ t} ⟶ G`: the finitely many local generators of `G` can be
chosen global
(`AlgebraicGeometry.Scheme.ProEt.exists_sections_forall_exists_mem_span_of_isFiniteTypeSections`),
and global sections which locally span give an epimorphism
(`AlgebraicGeometry.ProEtale.epi_biproductDescOfSections`). -/
theorem exists_epi_biproduct_constantSheaf_of_isFiniteTypeLocallyConstant [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ G) :
    ∃ (t : ℕ) (φ : (⨁ fun _ : Fin t => (constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} Λ)).obj (Functor.unitModule Λ)) ⟶ G), Epi φ := by
  have :=
    Stacks.ConstantSheaf.isFiniteTypeSections_ofFunctorObj_of_isFiniteTypeLocallyConstantModuleSheaf
      hG
  obtain ⟨n, s, hs⟩ :=
    Scheme.ProEt.exists_sections_forall_exists_mem_span_of_isFiniteTypeSections hX
    (Stacks.PresheafOfModules.ofFunctorObj Λ G.obj)
    ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{max (u + 1) w} Λ))).obj G).cond
  refine ⟨n, biproductDescOfSections fun i => (s i).eval (op (Scheme.ProEt.mk (𝟙 X))),
    epi_biproductDescOfSections _ fun V m => ?_⟩
  obtain ⟨S, hS, h⟩ := hs V m
  refine ⟨S, hS, fun W g hg => ?_⟩
  have hr : (Set.range fun i => (G.obj.map (Scheme.ProEt.toMkId W).op).hom
      ((s i).eval (op (Scheme.ProEt.mk (𝟙 X))))) = Set.range fun i => (s i).eval (op W) :=
    congrArg Set.range (funext fun i => (s i).2 (Scheme.ProEt.toMkId W).op)
  rw [hr]
  exact h g hg

end AlgebraicGeometry.ProEtale
