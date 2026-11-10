module

public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Factorization
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeAffine
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.SpanIdeal
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a quasi-regular immersion is finite locally free

A quasi-coherent sheaf of modules on a scheme is finite locally free as soon as every point
lies in an affine open over which its sections are a finite locally free module of sections of
the structure sheaf.  No rank is fixed: the index types of the local free presentations are
allowed to vary over the covering.

Consequently the conormal sheaf of a quasi-regular immersion `i : Z ⟶ X` is finite locally
free, which is condition (2) of [Stacks, Tag 063M] in the direction out of quasi-regularity.

## Main results

* `finite_projective_of_ringEquiv`: finiteness and projectivity of a module transfer along a
  ring isomorphism together with a compatible additive isomorphism.
* `Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion'`: a trivialisation found after
  restricting along an open immersion is a trivialisation over an open of the ambient scheme.
* `Stacks.Modules.isFiniteLocallyFree_restrict_fromSpec`: [Stacks, Tag 05JM] for a quasi-coherent
  sheaf over one affine open.
* `Stacks.Modules.isFiniteLocallyFree_of_module_affineOpens`: **the affine-local criterion**.
* `…RegularIdealSheaf.exists_affineOpen_isFiniteLocallyFree_sections_conormalSheaf`: **the
  sections of the conormal sheaf of a quasi-regular immersion over a suitable affine chart are a
  finite locally free module**.
* `…RegularIdealSheaf.isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion`: **the
  conormal sheaf of a quasi-regular immersion is finite locally free**.

## Implementation notes

The affine-local criterion is the rank-free counterpart of
`Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens`.

The conormal sheaf is named by an abbreviation whose module structure over the sections of the
structure sheaf is not in the syntactic shape the notation `Γ(C, U)` expects, so the finite local
freeness of its sections is proved for a sheaf of modules given together with an equation
identifying it with the conormal sheaf, and the equation is used at the end.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Lemma 31.20.5 (Tag 063M)](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Lemma 31.20.2 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 29.2.1 (Tag 01R3)](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Lemma 10.69.5 (Tag 08RK)](https://stacks.math.columbia.edu/tag/08RK)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr
  restrictFunctorId)

universe u

/-! ### Transport of finiteness and projectivity along a ring isomorphism -/

/-- **Finiteness and projectivity transfer along a ring isomorphism** together with a compatible
additive isomorphism of modules. -/
theorem finite_projective_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (σ : A ≃+* B)
    {N : Type u} [AddCommGroup N] [Module A N] {N' : Type u} [AddCommGroup N'] [Module B N']
    (φ : N ≃+ N') (hφ : ∀ (a : A) (x : N), φ (a • x) = σ a • φ x)
    (hfin : Module.Finite A N) (hproj : Module.Projective A N) :
    Module.Finite B N' ∧ Module.Projective B N' := by
  have _ := hproj
  have _ := RingHomInvPair.of_ringEquiv σ
  have _ := RingHomInvPair.of_ringEquiv_symm σ
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hfin.1
  refine ⟨⟨?_⟩, Module.Projective.of_equiv (σ := (σ : A →+* B)) (σ' := (σ.symm : B →+* A))
    { toFun := φ, invFun := φ.symm, map_add' := φ.map_add, map_smul' := hφ,
      left_inv := φ.left_inv, right_inv := φ.right_inv }⟩
  have key : ∀ x ∈ Submodule.span A s, φ x ∈ Submodule.span B (φ '' s) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [hφ]; exact Submodule.smul_mem _ _ hx
  rw [Submodule.fg_def]
  refine ⟨φ '' s, hsfin.image _, le_antisymm le_top fun y _ => ?_⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact key x (by rw [hs]; trivial)

namespace Stacks.Modules

variable {X : Scheme.{u}}

/-! ### The affine-local criterion -/

/-- **A trivialisation found after restricting along an open immersion is a trivialisation over
an open of the ambient scheme.**  If `F` restricted along an open immersion `g` is finite locally
free, then every point of the image of `g` has an open neighbourhood in `X` over which `F` is
free on a finite index type. -/
theorem exists_restrict_iso_free_of_isOpenImmersion' {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (F : X.Modules) (y : Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (F.restrict g)) :
    ∃ (U : X.Opens) (_ : g.base y ∈ U) (I : Type u) (_ : Finite I),
      Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} I) := by
  obtain ⟨W, hW, I, hI, ⟨e⟩⟩ := h y
  let e₀ := g.isoImage W
  let iso₂ : restrictFunctor e₀.hom ⋙ restrictFunctor e₀.inv ≅ 𝟭 _ :=
    (restrictFunctorComp e₀.inv e₀.hom).symm ≪≫
      restrictFunctorCongr e₀.inv_hom_id ≪≫ restrictFunctorId
  refine ⟨g ''ᵁ W, ⟨y, hW, rfl⟩, I, hI, ⟨?_⟩⟩
  exact (iso₂.app (F.restrict (g ''ᵁ W).ι)).symm ≪≫
    (restrictFunctor e₀.inv).mapIso ((restrictImageIso g W F).symm ≪≫ e) ≪≫
    (freeRestrictIso e₀.inv I).symm

/-- **The sections of a quasi-coherent module on an affine open determine its local freeness.**
If `Γ(F, U)` is a finite locally free `Γ(X, U)`-module, the restriction of `F` to `Spec Γ(X, U)`
is a finite locally free sheaf of modules. -/
theorem isFiniteLocallyFree_restrict_fromSpec (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (h : Module.IsFiniteLocallyFree Γ(X, U) Γ(F, U)) :
    Scheme.Modules.IsFiniteLocallyFree (F.restrict hU.fromSpec) :=
  Scheme.Modules.IsFiniteLocallyFree.of_iso (tildeIsoRestrictFromSpec F hU)
    ((tilde_isFiniteLocallyFree_iff Γ(X, U) Γ(F, U)).mpr h)

/-- **Finite local freeness is affine-local on sections.**  A quasi-coherent `𝒪_X`-module each of
whose points lies in an affine open `U` with `Γ(F, U)` a finite locally free `Γ(X, U)`-module is
a finite locally free `𝒪_X`-module. -/
theorem isFiniteLocallyFree_of_module_affineOpens (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Module.IsFiniteLocallyFree Γ(X, U.1) Γ(F, U.1)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  refine (Scheme.Modules.isFiniteLocallyFree_iff F).mp fun x => ?_
  obtain ⟨U, hxU, hmod⟩ := h x
  have hU : IsAffineOpen U.1 := U.2
  have hx : x ∈ Set.range hU.fromSpec.base := by
    rw [← Scheme.Hom.coe_opensRange, hU.opensRange_fromSpec]
    exact hxU
  obtain ⟨y, hy⟩ := hx
  obtain ⟨V, hxV, I, hI, hfree⟩ := exists_restrict_iso_free_of_isOpenImmersion' hU.fromSpec F y
    (isFiniteLocallyFree_restrict_fromSpec F hU hmod)
  exact ⟨V, hy ▸ hxV, I, hI, hfree⟩

end Stacks.Modules

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### The conormal module of a quasi-regular chart -/

variable {Z X : Scheme.{u}}

/-- **The conormal module of a quasi-regular immersion over a suitable affine chart is finite
locally free.**  Every point of the source of a quasi-regular immersion `i : Z ⟶ X` lies in an
affine open `U` of `Z` over which the sections of the conormal sheaf are a finite locally free
module over the functions on `U`. The conormal sheaf is given as a sheaf of modules `C` together
with an equation `hC` identifying it with `Stacks.Conormal.conormalSheaf i`. -/
@[ega "IV 19.1.3" "partial", sga "3 III 4.22" "partial", sga "3 III 4.6.2" "partial"]
theorem exists_affineOpen_isFiniteLocallyFree_sections_conormalSheaf (i : Z ⟶ X) [IsImmersion i]
    (h : IsQuasiRegularImmersion i) (C : Z.Modules)
    (hC : C = Stacks.Conormal.conormalSheaf i) (z : Z) :
    ∃ U : Z.affineOpens, z ∈ U.1 ∧ Module.IsFiniteLocallyFree Γ(Z, U.1) Γ(C, U.1) := by
  have hgen := (_root_.AlgebraicGeometry.isQuasiRegularIdealSheaf_iff_kerGeneratedBy
    i.liftCoborder).mp h
  obtain ⟨V, hzV, r, f, hspan, hqseq⟩ := hgen (i.liftCoborder.base z) (subset_closure ⟨z, rfl⟩)
  obtain ⟨I, e, he⟩ := Stacks.Conormal.exists_affineModel i.liftCoborder V.1 V.2
  have hI : RingHom.ker (i.liftCoborder.app V.1).hom = I := by
    have hk := Stacks.Conormal.ker_appLE_eq_of_affineModel i.liftCoborder V.1 V.2 I e he
    rwa [Scheme.Hom.appLE_eq_app] at hk
  subst hI
  have hsurj : Function.Surjective (i.liftCoborder.app V.1).hom :=
    i.liftCoborder.app_surjective V.1 V.2
  obtain ⟨hfin, hproj⟩ := Quasiregular.cotangent_finite_projective_of_quasiregular _
    (hspan ▸ Quasiregular.isQuasiregularIdeal_span_range f hqseq)
  have hc : (ModuleCat.restrictScalars (i.liftCoborder.app V.1).hom).obj
      (ModuleCat.of Γ(Z, i.liftCoborder ⁻¹ᵁ V.1) Γ(C, i.liftCoborder ⁻¹ᵁ V.1)) ≅
        ModuleCat.of Γ(i.coborderRange.toScheme, V.1)
          (RingHom.ker (i.liftCoborder.app V.1).hom).Cotangent := by
    subst hC
    exact Stacks.Conormal.pushforwardConormalIsoCotangent i i.coborderRange i.liftCoborder
      i.liftCoborder_ι V.1 V.2 _ e he
  refine ⟨⟨i.liftCoborder ⁻¹ᵁ V.1,
    Stacks.Conormal.isAffineOpen_preimage_of_affineModel i.liftCoborder V.1 _ e⟩, hzV, ?_⟩
  refine (Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr
    (finite_projective_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective hsurj) hc.toLinearEquiv.symm.toAddEquiv ?_ hfin hproj)
  intro a x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hsmul : (Ideal.Quotient.mk (RingHom.ker (i.liftCoborder.app V.1).hom) a) • x = a • x :=
    (IsScalarTower.algebraMap_smul _ a x).symm
  change hc.toLinearEquiv.symm _ = _
  rw [hsmul, hc.toLinearEquiv.symm.map_smul]
  rfl

/-! ### Finite local freeness of the conormal sheaf -/

/-- **The conormal sheaf of a quasi-regular immersion of schemes is finite locally free.** -/
@[ega "IV 19.1.3",
  sga "3 III 4.22" "partial",
  sga "3 III 4.6.2" "more general",
  sga "6 VII 1.6" "more general",
  sga "6 X 7.1" "more general"]
theorem isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion (i : Z ⟶ X) [IsImmersion i]
    (h : IsQuasiRegularImmersion i) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheaf i) := by
  obtain ⟨C, hC⟩ : ∃ C : Z.Modules, C = Stacks.Conormal.conormalSheaf i := ⟨_, rfl⟩
  have hqc : C.IsQuasicoherent := by
    subst hC
    exact Stacks.Conormal.conormalSheaf_isQuasicoherent i
  have key := Stacks.Modules.isFiniteLocallyFree_of_module_affineOpens C
    fun z => exists_affineOpen_isFiniteLocallyFree_sections_conormalSheaf i h C hC z
  rwa [hC] at key

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
