module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineEssentialSurjectivity
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ColimitsClosure

/-!
# The span condition on an affine slice site from the base change of the sections

On the slice site at an affine object `x` of a category fibred in groupoids over the big fppf
category of schemes, the span condition of Stacks 03DX has two halves: the sections of a
quasi-coherent module are locally combinations of the restrictions of its sections over `x`, and so
are the relations between any family of generators of it.  This file reduces both halves to a
single statement about the module alone, namely that over the objects of a prescribed class its
sections are the base change, along the ring map of global functions induced by the structural
morphism, of its sections over `x`.  That statement is
`AlgebraicGeometry.FibredSite.HasSectionBaseChangeOn`.

The generators half uses only surjectivity of the base-change comparison.  The relations half uses
its injectivity as well, together with the surjectivity on the sections over `x` of any covering
of the module by a coproduct of copies of the universe lift of the structure sheaf, which holds by
faithfully flat descent.

All names below are in the namespace `AlgebraicGeometry.FibredSite` unless qualified.

## Main definitions

* `HasSectionBaseChangeOn`: the sections of a sheaf of modules over the objects of a prescribed
  class of a slice of the associated fppf site are the base change of its sections over the object
  the slice is taken at.

## Main results

* `globalSectionSpan_eq_top_of_hasSectionBaseChangeOn`: the sections over an object of the class
  are combinations of the restrictions of the sections over `x`.
* `globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn`: the relations among the sections of a
  covering of the module over an affine object of the class are combinations of the relations over
  `x`.
* `surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn`: an epimorphism onto the module from a
  coproduct of copies of the universe lift of the structure sheaf is surjective on the sections
  over `x`.
* `hasSpannedRelationsOn_of_hasSectionBaseChangeOn` and
  `hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn`: the relations half of a global
  presentation in its unlocalised form, the second at the class of affine objects lying over a
  member of a covering family.
* `hasLocallySpannedRelations_of_hasSectionBaseChangeOn` and
  `isLocallySpannedBySections_of_hasSectionBaseChangeOn`: the two halves of the span condition at
  one affine object, and
  `isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn` their
  conjunction.
* `isAffineLocallySpanned_of_hasSectionBaseChangeOn`: the span condition on the affine slice sites
  from the base change of the sections.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe y z v w u t m

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

/-- **The sections over the objects of a class are the base change of the sections over the base.**
For every object `W` of a slice at `x` satisfying `Q`, the comparison carrying `c ⊗ₜ n` to `c`
times the restriction of `n` is a bijection from the base change, along the ring map induced on
global functions by the structural morphism of `W`, of the sections over `x` onto the sections over
`W`.

This is the content of the essential surjectivity of Stacks 03DX at the objects satisfying `Q`. -/
def HasSectionBaseChangeOn
    (N : SheafOfModules.{m} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (Q : Over x → Prop) : Prop :=
  ∀ W : Over x, Q W →
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
      (N.val.obj (op (Over.mk (𝟙 x)))))
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        (N.val.obj (op W)) := inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.val.obj (op W)))
    let _ : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := RingHom.toAlgebra
      ((BigFppfOver.toScheme B S hS).map
        (p.map (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x)).left)).appTop.hom
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (N.val.obj (op W)) :=
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
    have _ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Bijective
      ((({ toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
           map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
           map_smul' := fun c n =>
             (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl } :
            N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
              N.val.obj (op W))).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))

section Span

variable {N : SheafOfModules.{m} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  {Q : Over x → Prop}

/-- **The sections over an object where the comparison is surjective are combinations of the
restrictions of the sections over the base.**  Every section over such an object is a combination,
over the ring of sections of the structure sheaf there, of restrictions of sections over the object
the slice is taken at. -/
theorem globalSectionSpan_eq_top_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS p hp N Q) (W : Over x) (hW : Q W) :
    N.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mNW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.val.obj (op W)))
  let alg : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map
      (p.map (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x)).left)).appTop.hom
  let mNW' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (N.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  have twN : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let rN : N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
      N.val.obj (op W) :=
    { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
  exact SheafOfModules.globalSectionSpan_eq_top_of_baseChangeEquiv (Over.mkIdTerminal (X := x)) N
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (sectionRingEquivGamma B S hS p hp .fppf W).symm.toRingHom (fun _ _ => rfl)
    (rN.liftBaseChange Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
    (hN W hW).2 fun n => by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl

end Span

section Kernel

variable {N : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  {Q : Over x → Prop}

/-- **The relations among the sections of a covering of the module over an affine object of the
class are combinations of the relations over the base.**

Let `b₂ : P₂ ⟶ N` be a morphism onto `N` from a coproduct of copies of the universe lift of the
structure sheaf which is surjective on the sections over the affine object `x` the slice is taken
at, and let `k : Z ⟶ P₂` be a kernel of it.  Then the sections of `Z` over an affine object `W` of
the class are combinations, over the ring of sections of the structure sheaf there, of restrictions
of its sections over `x`. -/
theorem globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS p hp N Q) {I₂ : Type y}
    {P₂ Z : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
      (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N)
    (hsurj₂ : Function.Surjective (b₂.val.app (op (Over.mk (𝟙 x)))))
    (k : Z ⟶ P₂) (hk : k ≫ b₂ = 0) (hZ : IsLimit (KernelFork.ofι k hk))
    (hx : IsAffineOver B S hS (p.obj x))
    (W : Over x) (hQW : Q W) (hW : IsAffineOver B S hS (p.obj W.left)) :
    Z.globalSectionSpan (Over.mkIdTerminal (X := x)) W = ⊤ := by
  let mP₂T : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P₂.val.obj (op (Over.mk (𝟙 x)))))
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mP₂W : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (P₂.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (P₂.val.obj (op W)))
  let mNW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.val.obj (op W)))
  let mZW : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (Z.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (Z.val.obj (op W)))
  let alg : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map
      (p.map (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x)).left)).appTop.hom
  let mP₂W' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (P₂.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  let mNW' : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (N.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  have twP₂ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (P₂.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let rP₂ : P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] P₂.val.obj (op W) :=
    { toFun := fun q => P₂.val.map (Over.mkIdTerminal.from W).op q
      map_add' := map_add (P₂.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c q =>
        (P₂.val.map_smul (Over.mkIdTerminal.from W).op c q).symm ▸ rfl }
  have hP₂bij := SheafOfModules.bijective_liftBaseChange_of_tautBasis ι₂
    (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 x))
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx
      (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
    (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ W hW
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl))
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx _ _ i)
    (fun i => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ W hW _ _ i) rP₂
    (fun _ => rfl)
  refine Submodule.eq_top_iff'.2 fun z => ?_
  have hzk : b₂.val.app (op W) (k.val.app (op W) z) = 0 := by
    have h := congr($(hk).val.app (op W) z)
    rwa [SheafOfModules.comp_val] at h
  let bT₂ : P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] N.val.obj (op (Over.mk (𝟙 x))) :=
    { toFun := fun q => b₂.val.app (op (Over.mk (𝟙 x))) q
      map_add' := map_add (b₂.val.app (op (Over.mk (𝟙 x)))).hom
      map_smul' := fun c q => (b₂.val.app (op (Over.mk (𝟙 x)))).hom.map_smul c q }
  have hkey := Module.BaseChange.mem_span_image_ker_of_liftBaseChange
    (A := Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤))
    (Bc := Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 x)))) (NT := N.val.obj (op (Over.mk (𝟙 x))))
    (PW := P₂.val.obj (op W)) (NW := N.val.obj (op W)) bT₂
    { toFun := fun q => b₂.val.app (op W) q
      map_add' := map_add (b₂.val.app (op W)).hom
      map_smul' := fun c q => (b₂.val.app (op W)).hom.map_smul c q }
    rP₂
    { toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
      map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
      map_smul' := fun c n =>
        (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl }
    (fun q => (PresheafOfModules.naturality_apply b₂.val
      (Over.mkIdTerminal.from W).op q).symm)
    hP₂bij.2 (hN W hQW).1 hsurj₂ hzk
  have hspan : ∀ q ∈ Submodule.span Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (rP₂ '' (LinearMap.ker bT₂ : Set (P₂.val.obj (op (Over.mk (𝟙 x)))))),
      ∃ ζ ∈ Z.globalSectionSpan (Over.mkIdTerminal (X := x)) W, k.val.app (op W) ζ = q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      obtain ⟨ζ₀, hζ₀⟩ := SheafOfModules.mem_range_val_app_of_isLimit_kernelFork hZ
        (op (Over.mk (𝟙 x))) (show b₂.val.app (op (Over.mk (𝟙 x))) q₀ = 0 from hq₀)
      refine ⟨Z.val.map (Over.mkIdTerminal.from W).op ζ₀,
        Submodule.subset_span ⟨ζ₀, rfl⟩, ?_⟩
      exact (PresheafOfModules.naturality_apply k.val (Over.mkIdTerminal.from W).op ζ₀).trans
        (congrArg (fun y => P₂.val.map (Over.mkIdTerminal.from W).op y) hζ₀)
    | zero => exact ⟨0, zero_mem _, map_zero (k.val.app (op W)).hom⟩
    | add q q' _ _ hζ hζ' =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      obtain ⟨ζ', hζm', hζe'⟩ := hζ'
      exact ⟨ζ + ζ', add_mem hζm hζm', by
        rw [map_add (k.val.app (op W)).hom, hζe, hζe']⟩
    | smul c q _ hζ =>
      obtain ⟨ζ, hζm, hζe⟩ := hζ
      exact ⟨c • ζ, Submodule.smul_mem _ c hζm, by rw [map_smul, hζe]⟩
  obtain ⟨ζ, hζm, hζe⟩ := hspan _ hkey
  exact SheafOfModules.injective_val_app_of_isLimit_kernelFork hZ (op W) hζe ▸ hζm

end Kernel

section Surjectivity

variable
  [HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x) AddCommGrpCat.{max t u}]
  [((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
    AddCommGrpCat.{max t u}]
  {N : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
  {Q : Over x → Prop}

/-- **An epimorphism onto the module from a coproduct of copies of the universe lift of the
structure sheaf is surjective on the sections over the affine object the slice is taken at.**  Here
`x` is affine, the sections of `N` over the objects of the class `Q` are the base change of its
sections over `x`, and `Q` contains every affine object admitting a morphism to a member of a
covering family `Y₀` of `x`. -/
theorem surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn
    (hN : HasSectionBaseChangeOn B S hS p hp N Q)
    (hx : IsAffineOver B S hS (p.obj x))
    {ι : Type z} {Y₀ : ι → Over x} (g₀ : ∀ j, Y₀ j ⟶ Over.mk (𝟙 x))
    (hcov₀ : Sieve.ofArrows Y₀ g₀ ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hQfac : ∀ (W : Over x) (j : ι), (W ⟶ Y₀ j) → IsAffineOver B S hS (p.obj W.left) → Q W)
    {I₂ : Type y}
    {P₂ : SheafOfModules.{max t u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (ι₂ : ∀ _ : I₂, SheafOfModules.uliftForPresentation.{max v w, w, u, u, t}
      (SheafOfModules.unit ((ringStructureSheafCore B S hS p hp .fppf).over x)) ⟶ P₂)
    (hP₂ : IsColimit (Cofan.mk P₂ ι₂)) (b₂ : P₂ ⟶ N) [Epi b₂] :
    Function.Surjective (b₂.val.app (op (Over.mk (𝟙 x)))) := by
  refine SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange.{0} b₂ fun Sv hSv => ?_
  obtain ⟨m, Y, g, hYaff, hmem, hcov, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le_over B S hS p hp (𝟙 x) hx
      (Sv ⊓ Sieve.ofArrows Y₀ g₀)
      (((BigFppfOver.associatedTopology B S hS p .fppf).over x).intersection_covering hSv hcov₀)
  have hg : ∀ i, g i = Over.mkIdTerminal.from (Y i) :=
    fun i => (Over.mkIdTerminal (X := x)).hom_ext (g i) _
  have hQY : ∀ i, Q (Y i) := fun i => by
    obtain ⟨j, c, -⟩ := (Sieve.mem_ofArrows_iff Y₀ g₀ (g i)).1 (hmem i).2
    exact hQfac (Y i) j c (hYaff i)
  have hfppf' : Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left))
      (fun i => (BigFppfOver.toScheme B S hS).map
        (p.map (Over.mkIdTerminal.from (Y i) : Y i ⟶ Over.mk (𝟙 x)).left)) ∈
      Scheme.fppfPrecoverage
        ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left)) := by
    simpa only [hg] using hfppf
  refine ⟨Fin m, Y, fun i => Over.mkIdTerminal.from (Y i),
    fun i => by simpa only [hg i] using (hmem i).1, fun nn hnn => ?_⟩
  let mP₂T : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (P₂.val.obj (op (Over.mk (𝟙 x)))))
  let mNT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mP₂Y : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (P₂.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (P₂.val.obj (op (Y i))))
  let mNY : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (N.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (N.val.obj (op (Y i))))
  let alg : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := fun i => RingHom.toAlgebra
    ((BigFppfOver.toScheme B S hS).map
      (p.map (Over.mkIdTerminal.from (Y i) : Y i ⟶ Over.mk (𝟙 x)).left)).appTop.hom
  let alg' : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := alg
  let mP₂Y' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (P₂.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  let mNY' : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Y i))) := fun i =>
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  have twP₂ : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (P₂.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twN : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (N.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS p Y
      (fun i => Over.mkIdTerminal.from (Y i)) hx hYaff hfppf' fun _ => rfl
  let rP₂ : ∀ i, P₂.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] P₂.val.obj (op (Y i)) := fun i =>
    { toFun := fun q => P₂.val.map (Over.mkIdTerminal.from (Y i)).op q
      map_add' := map_add (P₂.val.map (Over.mkIdTerminal.from (Y i)).op).hom
      map_smul' := fun c q =>
        (P₂.val.map_smul (Over.mkIdTerminal.from (Y i)).op c q).symm ▸ rfl }
  have hP₂bij : ∀ i, Function.Bijective ((rP₂ i).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := fun i =>
    SheafOfModules.bijective_liftBaseChange_of_tautBasis ι₂
      (Over.mkIdTerminal.from (Y i) : Y i ⟶ Over.mk (𝟙 x))
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx
        (sectionRingEquivGamma B S hS p hp .fppf (Over.mk (𝟙 x))) (fun _ _ => rfl))
      (tautBasisOfIsAffineOverCoeffs B S hS p hp ι₂ hP₂ (Y i) (hYaff i)
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)) (fun _ _ => rfl))
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Over.mk (𝟙 x)) hx _ _ j)
      (fun j => tautBasisOfIsAffineOverCoeffs_apply B S hS p hp ι₂ hP₂ (Y i) (hYaff i) _ _ j)
      (rP₂ i) fun _ => rfl
  exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
    (fun i => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
    (PT := P₂.val.obj (op (Over.mk (𝟙 x)))) (NT := N.val.obj (op (Over.mk (𝟙 x))))
    (PW := fun i => P₂.val.obj (op (Y i))) (NW := fun i => N.val.obj (op (Y i)))
    { toFun := fun q => b₂.val.app (op (Over.mk (𝟙 x))) q
      map_add' := map_add (b₂.val.app (op (Over.mk (𝟙 x)))).hom
      map_smul' := fun c q => (b₂.val.app (op (Over.mk (𝟙 x)))).hom.map_smul c q }
    (fun i =>
      { toFun := fun q => b₂.val.app (op (Y i)) q
        map_add' := map_add (b₂.val.app (op (Y i))).hom
        map_smul' := fun c q => (b₂.val.app (op (Y i))).hom.map_smul c q })
    rP₂
    (fun i =>
      { toFun := fun n => N.val.map (Over.mkIdTerminal.from (Y i)).op n
        map_add' := map_add (N.val.map (Over.mkIdTerminal.from (Y i)).op).hom
        map_smul' := fun c n =>
          (N.val.map_smul (Over.mkIdTerminal.from (Y i)).op c n).symm ▸ rfl })
    (fun i q => (PresheafOfModules.naturality_apply b₂.val
      (Over.mkIdTerminal.from (Y i)).op q).symm)
    (fun i => (hP₂bij i).2) (fun i => (hN (Y i) (hQY i)).1)
    fun i => by obtain ⟨q, hq⟩ := hnn i; exact ⟨q, hq⟩

end Surjectivity

section Assembly

variable (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))

/-- **The relations half of a global presentation in its unlocalised form, at the objects of the
class.**  The kernel of every covering of the universe lift of the module by a coproduct of copies
of the universe lift of the structure sheaf has its sections over an object of the class spanned by
the restrictions of its sections over `x`. -/
theorem hasSpannedRelationsOn_of_hasSectionBaseChangeOn
    (hx : IsAffineOver B S hS (p.obj x)) {Q : Over x → Prop}
    (hQaff : ∀ W : Over x, Q W → IsAffineOver B S hS (p.obj W.left))
    {ι : Type z} {Y : ι → Over x} (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hQfac : ∀ (W : Over x) (j : ι), (W ⟶ Y j) → IsAffineOver B S hS (p.obj W.left) → Q W)
    (hM : HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M) Q) :
    M.HasSpannedRelationsOn (Over.mkIdTerminal (X := x)) Q := by
  have _ : HasSheafify ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      AddCommGrpCat.{max v w u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max v w u, w, max v w} _
  have _ : ((BigFppfOver.associatedTopology B S hS p .fppf).over x).WEqualsLocallyBijective
      AddCommGrpCat.{max v w u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max v w u, max v w, w} _
  intro I₂ P₂ ι₂ hP₂ b₂ hb₂ Z k hk hZ W hW
  exact globalSectionSpan_eq_top_ker_of_hasSectionBaseChangeOn B S hS p hp hM ι₂ hP₂ b₂
    (surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn B S hS p hp hM hx g hcov hQfac
      ι₂ hP₂ b₂) k hk hZ hx W hW (hQaff W hW)

/-- **The relations half of a global presentation at the affine objects lying over a member of a
covering family.**  This is
`AlgebraicGeometry.FibredSite.hasSpannedRelationsOn_of_hasSectionBaseChangeOn` for the class of
affine objects of the slice admitting a morphism to a member of the family. -/
theorem hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn
    (hx : IsAffineOver B S hS (p.obj x))
    {ι : Type z} {Y : ι → Over x} (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hM : HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M)
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.HasSpannedRelationsOn (Over.mkIdTerminal (X := x))
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j) :=
  hasSpannedRelationsOn_of_hasSectionBaseChangeOn B S hS p hp M hx (fun _ h => h.1) g hcov
    (fun _ j c hW => ⟨hW, j, ⟨c⟩⟩) hM

/-- **The relations between any family of generators of the module are locally spanned by their
sections over the affine object the slice is taken at**, when the sections of the universe lift of
the module over the affine objects lying over a member of a covering family of `x` are the base
change of its sections over `x`. -/
theorem hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    (hx : IsAffineOver B S hS (p.obj x))
    {ι : Type z} {Y : ι → Over x} (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hM : HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M)
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.HasLocallySpannedRelations (Over.mkIdTerminal (X := x)) :=
  hasLocallySpannedRelations_over_of_cover B S hS p hp x (Over.mkIdTerminal (X := x)) M Y g hcov
    (hasSpannedRelationsOn_over_of_hasSectionBaseChangeOn B S hS p hp M hx g hcov hM)

/-- **The module is locally spanned by its sections over the affine object the slice is taken
at**, when the sections of its universe lift over the affine objects lying over a member of a
covering family of `x` are the base change of its sections over `x`. -/
theorem isLocallySpannedBySections_of_hasSectionBaseChangeOn
    {ι : Type z} {Y : ι → Over x} (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hM : HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M)
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.IsLocallySpannedBySections (Over.mkIdTerminal (X := x)) :=
  isLocallySpannedBySections_over_of_forall_affine_of_cover B S hS p hp x
    (Over.mkIdTerminal (X := x)) M Y g hcov fun j W hW a => by
      refine Submodule.eq_top_iff'.2 fun n => ?_
      refine SheafOfModules.down_mem_globalSectionSpan_of_mem_uliftForPresentation
        (Over.mkIdTerminal (X := x)) M W (x := ULift.up n) ?_
      rw [globalSectionSpan_eq_top_of_hasSectionBaseChangeOn B S hS p hp hM W ⟨hW, j, ⟨a⟩⟩]
      exact Submodule.mem_top

/-- **Both halves of the span condition at an affine object, from the base change of the
sections.**  This is the body of `AlgebraicGeometry.FibredSite.IsAffineLocallySpanned` at one
affine object, with quasi-coherence of the module replaced by the base-change comparisons at the
affine objects lying over the members of one covering family of it. -/
theorem isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    (hx : IsAffineOver B S hS (p.obj x))
    {ι : Type z} {Y : ι → Over x} (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hM : HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} M)
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    M.IsLocallySpannedBySections (Over.mkIdTerminal (X := x)) ∧
      M.HasLocallySpannedRelations (Over.mkIdTerminal (X := x)) :=
  ⟨isLocallySpannedBySections_of_hasSectionBaseChangeOn B S hS p hp M g hcov hM,
    hasLocallySpannedRelations_of_hasSectionBaseChangeOn B S hS p hp M hx g hcov hM⟩

end Assembly

/-- **The span condition on the affine slice sites, from the base change of the sections.**  If
every quasi-coherent module on the slice site at an affine object has a covering family of that
object over whose affine objects its sections are the base change of its sections over the object
itself, then the span condition
`AlgebraicGeometry.FibredSite.IsAffineLocallySpanned` holds.

That is the hypothesis of
`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_span` and of
`AlgebraicGeometry.FibredSite.inclusion_preservesColimits_of_span`, so the colimit clause of Stacks
06WN(1) follows from the base change of the sections alone. -/
theorem isAffineLocallySpanned_of_hasSectionBaseChangeOn
    (hbc : ∀ (i : AffineObjects B S hS p)
      (N : SheafOfModules.{u}
        ((ringStructureSheafCore B S hS p hp .fppf).over (affineObj B S hS p i))),
      N.IsQuasicoherentOnSite →
        ∃ (ι : Type z) (Y : ι → Over (affineObj B S hS p i))
          (g : ∀ j, Y j ⟶ Over.mk (𝟙 (affineObj B S hS p i))),
          Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over
              (affineObj B S hS p i)) (Over.mk (𝟙 (affineObj B S hS p i))) ∧
            HasSectionBaseChangeOn B S hS p hp
              (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} N)
              fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j)) :
    IsAffineLocallySpanned B S hS p hp := fun i N hN => by
  obtain ⟨ι, Y, g, hcov, hbc'⟩ := hbc i N hN
  exact isLocallySpannedBySections_and_hasLocallySpannedRelations_of_hasSectionBaseChangeOn
    B S hS p hp N i.property g hcov hbc'

end AlgebraicGeometry.FibredSite

end
