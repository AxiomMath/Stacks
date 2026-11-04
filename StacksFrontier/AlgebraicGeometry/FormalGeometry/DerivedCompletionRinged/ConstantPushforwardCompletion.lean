module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantDerivedPullbackAdic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedLimits
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image and derived completion with constant Noetherian coefficients

Let `f : Sh(𝒟) ⟶ Sh(𝒞)` be a morphism of topoi, `Λ` a Noetherian ring and `I ⊂ Λ` an ideal, and
read `f` as the morphism of ringed topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` of
`MorphismOfTopoi.constantRingedToposHom`. Derived completion is along `IΛ̲` on both sides. This
file proves that `Rf_*` and derived completion commute up to isomorphism:

`(Rf_*E)^∧ ≅ Rf_*(E^∧)` for every `E` in `D(𝒟, Λ)`.

By [Stacks, Tag 099M] the left-hand side is a derived limit of the tower
`n ↦ Rf_*E ⊗^𝐋_Λ (Λ/Iⁿ)̲`, and the right-hand side is a derived limit of
`n ↦ Rf_*(E ⊗^𝐋_Λ (Λ/Iⁿ)̲)`, because `Rf_*` commutes with derived limits ([Stacks, Tag 0A07]).
The two towers are pro-isomorphic
(`MorphismOfTopoi.nonempty_proIso_constantAdicTower_derivedPushforward`), and derived limits of
pro-isomorphic towers are isomorphic ([Stacks, Tag 0H9L]).

## Main results

* `MorphismOfTopoi.isDerivedLimit_constantAdicTower_derivedPushforward`: `Rf_*` carries the
  derived limit of `n ↦ E ⊗^𝐋 (Λ/Iⁿ)̲` to a derived limit of its image.
* `MorphismOfTopoi.nonempty_iso_derivedCompletion_derivedPushforward`: `(Rf_*E)^∧ ≅ Rf_*(E^∧)`.

## References

* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry
open Stacks.Homology
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

section Shift

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **Derived completeness is stable under shifts.** On each slice the derived restriction
commutes with the shift, and the shift is an exact linear equivalence, so it preserves the
Milnor condition at every local section. -/
theorem isDerivedComplete_shift
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsDerivedComplete.{u, u, u, u} X I K) (n : ℤ) :
    IsDerivedComplete.{u, u, u, u} X I (K⟦n⟧) := by
  intro U f hf
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U
  let A := SheafOfModules.{u} R
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ V : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj V) := fun V ↦ by
    show IsMulCommutative (X.O.obj.obj (Opposite.op V.unop.left))
    infer_instance
  let F := SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  obtain ⟨hAdd, hLim, hColim, hProducts, hComplete⟩ := hK U f hf
  let : F.Additive := hAdd
  let : PreservesFiniteLimits F := hLim
  let : PreservesFiniteColimits F := hColim
  let : HasProductsOfShape ℕ (DerivedCategory A) := hProducts
  refine ⟨hAdd, hLim, hColim, hProducts, ?_⟩
  refine (isDerivedCompleteAt_iff_of_iso (A := CatCenter A)
    ((F.mapDerivedCategory.commShiftIso n).app K).symm _).1 ?_
  exact isDerivedCompleteAt_map (A := CatCenter A) (shiftFunctor (DerivedCategory A) n) _ _
    hComplete

end Shift

section Reflector

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- The map out of the derived completion produced by the universal property, composed with the
unit, is the map it was produced from. -/
private theorem unit_comp_map_homEquiv_symm
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {M : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I)} (g : K ⟶ M.obj) :
    (derivedCompletionUnit X I).app K ≫
        (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map
          (((derivedCompletionAdjunction X I).homEquiv K M).symm g) = g := by
  have h := (derivedCompletionAdjunction X I).homEquiv_unit K M
    (((derivedCompletionAdjunction X I).homEquiv K M).symm g)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Every map from an object into a derived-complete object factors through the derived
completion unit. -/
theorem exists_derivedCompletionUnit_comp
    {K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsDerivedComplete.{u, u, u, u} X I M) (g : K ⟶ M) :
    ∃ g' : (derivedCompletion X I).obj K ⟶ M, g = (derivedCompletionUnit X I).app K ≫ g' := by
  let M' : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} X I) := ⟨M, hM⟩
  exact ⟨_, (unit_comp_map_homEquiv_symm X I (M := M') g).symm⟩

/-- **The universal property of the derived completion after a shift**, uniqueness: maps out of
`K^∧⟦n⟧` into a derived-complete object are determined by their composite with the shifted
unit. -/
theorem eq_zero_of_shift_derivedCompletionUnit_comp_eq_zero
    {K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsDerivedComplete.{u, u, u, u} X I M) (n : ℤ)
    {h : ((derivedCompletion X I).obj K)⟦n⟧ ⟶ M}
    (hh : ((derivedCompletionUnit X I).app K)⟦n⟧' ≫ h = 0) : h = 0 := by
  let e := shiftFunctorCompIsoId (DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n (-n) (add_neg_cancel n)
  have h₁ : (derivedCompletionUnit X I).app K ≫
      (e.inv.app ((derivedCompletion X I).obj K) ≫ h⟦-n⟧') = 0 := by
    have hn : (derivedCompletionUnit X I).app K ≫ e.inv.app ((derivedCompletion X I).obj K) =
        e.inv.app K ≫ (((derivedCompletionUnit X I).app K)⟦n⟧')⟦-n⟧' :=
      e.inv.naturality _
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hh, Functor.map_zero,
      comp_zero]
  have h₂ := hom_ext_derivedCompletionUnit X I (isDerivedComplete_shift X I hM (-n))
    (h₁.trans comp_zero.symm)
  have h₃ : h⟦-n⟧' = 0 := by
    rw [← cancel_epi (e.inv.app ((derivedCompletion X I).obj K)), h₂, comp_zero]
  apply (shiftFunctor _ (-n)).map_injective
  rw [h₃, Functor.map_zero]

/-- **The universal property of the derived completion after a shift**, existence: every map
`K⟦n⟧ ⟶ M` into a derived-complete object factors through the shifted unit. -/
theorem exists_shift_derivedCompletionUnit_comp
    {K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsDerivedComplete.{u, u, u, u} X I M) (n : ℤ) (g : K⟦n⟧ ⟶ M) :
    ∃ g' : ((derivedCompletion X I).obj K)⟦n⟧ ⟶ M,
      g = ((derivedCompletionUnit X I).app K)⟦n⟧' ≫ g' := by
  let e := shiftFunctorCompIsoId (DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (-n) n (neg_add_cancel n)
  let g₀ : K ⟶ M⟦-n⟧ := (shiftFunctor _ n).preimage (g ≫ e.inv.app M)
  obtain ⟨g₁, hg₁⟩ := exists_derivedCompletionUnit_comp X I (isDerivedComplete_shift X I hM (-n)) g₀
  refine ⟨g₁⟦n⟧' ≫ e.hom.app M, ?_⟩
  have : (shiftFunctor _ n).map g₀ = g ≫ e.inv.app M := (shiftFunctor _ n).map_preimage _
  rw [← Category.assoc, ← Functor.map_comp, ← hg₁, this, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id g).symm

/-- If the derived completion of `K` is zero, every map from `K` to a derived-complete object is
zero. -/
theorem eq_zero_of_isZero_derivedCompletion
    {K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsZero ((derivedCompletion X I).obj K)) (hM : IsDerivedComplete.{u, u, u, u} X I M)
    (g : K ⟶ M) : g = 0 := by
  obtain ⟨g', rfl⟩ := exists_derivedCompletionUnit_comp X I hM g
  rw [hK.eq_of_src g' 0, comp_zero]

/-- If every map from `K` to a derived-complete object is zero, the derived completion of `K` is
zero. -/
theorem isZero_derivedCompletion_of_forall_eq_zero
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : ∀ M, IsDerivedComplete.{u, u, u, u} X I M → ∀ g : K ⟶ M, g = 0) :
    IsZero ((derivedCompletion X I).obj K) := by
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext_derivedCompletionUnit X I (isDerivedComplete_derivedCompletion_obj X I K) ?_
  rw [Category.comp_id, comp_zero]
  exact hK _ (isDerivedComplete_derivedCompletion_obj X I K) _

/-- **The fibre of the derived completion unit is left orthogonal to the derived-complete
objects**, together with its shift: in a distinguished triangle `N ⟶ K ⟶ K^∧ ⟶ N⟦1⟧` whose
second map is the unit, every map from `N` or from `N⟦1⟧` to a derived-complete object is zero. -/
theorem eq_zero_of_distTriang_derivedCompletionUnit
    {N K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : N ⟶ K) (b : (derivedCompletion X I).obj K ⟶ N⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((derivedCompletionUnit X I).app K) b ∈ distTriang _)
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hM : IsDerivedComplete.{u, u, u, u} X I M) :
    (∀ g : N⟦(1 : ℤ)⟧ ⟶ M, g = 0) ∧ ∀ g : N ⟶ M, g = 0 := by
  have h₁ : ∀ {M : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))},
      IsDerivedComplete.{u, u, u, u} X I M → ∀ g : N⟦(1 : ℤ)⟧ ⟶ M, g = 0 := by
    intro M hM φ
    have hb : b ≫ φ = 0 := by
      refine hom_ext_derivedCompletionUnit X I hM ?_
      have h0 : (derivedCompletionUnit X I).app K ≫ b = 0 := comp_distTriang_mor_zero₂₃ _ hT
      rw [← Category.assoc, h0, zero_comp, comp_zero]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) φ hb
    obtain ⟨g', hg'⟩ := exists_shift_derivedCompletionUnit_comp X I (K := K) hM 1 g
    have hz : (-a⟦(1 : ℤ)⟧') ≫ ((derivedCompletionUnit X I).app K)⟦(1 : ℤ)⟧' = 0 := by
      have h0 : a ≫ (derivedCompletionUnit X I).app K = 0 := comp_distTriang_mor_zero₁₂ _ hT
      rw [Preadditive.neg_comp, ← Functor.map_comp, h0, Functor.map_zero, neg_zero]
    change φ = (-a⟦(1 : ℤ)⟧') ≫ g at hg
    rw [hg, hg', ← Category.assoc, hz, zero_comp]
  exact ⟨h₁ hM, fun g => (shiftFunctor _ (1 : ℤ)).map_injective
    ((h₁ (isDerivedComplete_shift X I hM 1) _).trans (Functor.map_zero _ _ _).symm)⟩

end Reflector

section Comparison

variable {X Y : RingedSite.{u, u, u}}
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (I' : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} Y I')).IsRightAdjoint]
  (R : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (hR : ∀ K, IsDerivedComplete.{u, u, u, u} X I K → IsDerivedComplete.{u, u, u, u} Y I' (R.obj K))

omit [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint] in
/-- The map out of the derived completion produced by the universal property, composed with the
unit, is the map it was produced from. -/
theorem derivedCompletionUnit_comp_homEquiv_symm
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {M : ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} Y I')} (g : K ⟶ M.obj) :
    (derivedCompletionUnit Y I').app K ≫
        (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} Y I')).map
          (((derivedCompletionAdjunction Y I').homEquiv K M).symm g) = g :=
  unit_comp_map_homEquiv_symm Y I' g

/-- **The canonical comparison `(R K)^∧ ⟶ R(K^∧)`** for a functor `R` between derived categories
of ringed sites which carries derived-complete objects to derived-complete objects: the map out
of the derived completion of `R K` determined by the universal property of derived completion
from `R(K ⟶ K^∧)`, the target `R(K^∧)` being derived complete. -/
def derivedCompletionComparisonApp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedCompletion Y I').obj (R.obj K) ⟶ R.obj ((derivedCompletion X I).obj K) :=
  (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} Y I')).map
    (((derivedCompletionAdjunction Y I').homEquiv (R.obj K)
      (⟨R.obj ((derivedCompletion X I).obj K),
          hR _ (isDerivedComplete_derivedCompletion_obj X I K)⟩ :
        ObjectProperty.FullSubcategory (IsDerivedComplete.{u, u, u, u} Y I'))).symm
      (R.map ((derivedCompletionUnit X I).app K)))

/-- **The comparison is the map determined by the universal property of derived completion**:
composed with the unit `R K ⟶ (R K)^∧` it is `R` applied to the unit `K ⟶ K^∧`. -/
theorem derivedCompletionUnit_comp_derivedCompletionComparisonApp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedCompletionUnit Y I').app (R.obj K) ≫ derivedCompletionComparisonApp I I' R hR K =
      R.map ((derivedCompletionUnit X I).app K) :=
  derivedCompletionUnit_comp_homEquiv_symm I' _

/-- **The canonical comparison `R ⋙ (-)^∧ ⟶ (-)^∧ ⋙ R`**, natural in the object: its component
at `K` is `derivedCompletionComparisonApp`, the map `(R K)^∧ ⟶ R(K^∧)` produced by the universal
property of derived completion. -/
def derivedCompletionComparison :
    R ⋙ derivedCompletion Y I' ⟶ derivedCompletion X I ⋙ R where
  app K := derivedCompletionComparisonApp I I' R hR K
  naturality {K K'} φ := by
    refine hom_ext_derivedCompletionUnit Y I'
      (hR _ (isDerivedComplete_derivedCompletion_obj X I K')) ?_
    have hY : (derivedCompletionUnit Y I').app (R.obj K) ≫
        (derivedCompletion Y I').map (R.map φ) =
        R.map φ ≫ (derivedCompletionUnit Y I').app (R.obj K') :=
      ((derivedCompletionUnit Y I').naturality (R.map φ)).symm
    have hX : (derivedCompletionUnit X I).app K ≫ (derivedCompletion X I).map φ =
        φ ≫ (derivedCompletionUnit X I).app K' :=
      ((derivedCompletionUnit X I).naturality φ).symm
    change (derivedCompletionUnit Y I').app (R.obj K) ≫
        ((derivedCompletion Y I').map (R.map φ) ≫ derivedCompletionComparisonApp I I' R hR K') =
      (derivedCompletionUnit Y I').app (R.obj K) ≫
        (derivedCompletionComparisonApp I I' R hR K ≫ R.map ((derivedCompletion X I).map φ))
    rw [← Category.assoc, hY, Category.assoc,
      derivedCompletionUnit_comp_derivedCompletionComparisonApp, ← Category.assoc,
      derivedCompletionUnit_comp_derivedCompletionComparisonApp, ← R.map_comp, ← R.map_comp, hX]

/-- The component of `derivedCompletionComparison` at `K` is `derivedCompletionComparisonApp`. -/
theorem derivedCompletionComparison_app
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedCompletionComparison I I' R hR).app K = derivedCompletionComparisonApp I I' R hR K :=
  rfl

end Comparison

end AlgebraicGeometry.RingedSite

namespace MorphismOfTopoi

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D} (Λ : Type u) [CommRing Λ]
  (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))

/-- The derived pushforward `Rf_*` along `constantRingedToposHom Λ f` is a right adjoint. -/
instance isRightAdjoint_constantDerivedPushforward :
    (constantDerivedPushforward Λ f).IsRightAdjoint :=
  (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
    (constantRingedToposHom Λ f)).isRightAdjoint

/-- The derived pushforward `Rf_*` along `constantRingedToposHom Λ f` commutes with shifts. -/
instance commShift_constantDerivedPushforward :
    (constantDerivedPushforward Λ f).CommShift ℤ :=
  (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
    (constantRingedToposHom Λ f)).rightAdjointCommShift ℤ

/-- The derived pushforward `Rf_*` along `constantRingedToposHom Λ f` is a triangulated functor. -/
instance isTriangulated_constantDerivedPushforward :
    (constantDerivedPushforward Λ f).IsTriangulated :=
  letI : (constantDerivedPullback Λ f).IsTriangulated :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated
      (constantRingedToposHom Λ f)
  letI : (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
      (constantRingedToposHom Λ f)).CommShift ℤ :=
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
      (constantRingedToposHom Λ f)).commShift_of_leftAdjoint ℤ
  (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
    (constantRingedToposHom Λ f)).isTriangulated_rightAdjoint

/-- **[Stacks, Tag 0A07] along `MorphismOfTopoi.constantRingedToposHom`**: `Rf_*` carries a derived
limit of a tower to a derived limit of the image tower. -/
theorem isDerivedLimit_map_constantDerivedPushforward
    (T : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)))
    [HasProduct fun n : ℕ ↦ T.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (T ⋙ constantDerivedPushforward Λ f).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)))
    (hL : IsDerivedLimit T L) :
    IsDerivedLimit (T ⋙ constantDerivedPushforward Λ f)
      ((constantDerivedPushforward Λ f).obj L) := by
  obtain ⟨_, hl⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
    (constantDerivedPushforward Λ f) T L hL
  convert hl

variable [IsNoetherianRing Λ] (I : Ideal Λ)

/-- **`Rf_*E` is a derived limit of the tower `n ↦ Rf_*E ⊗^𝐋_Λ (Λ/Iⁿ)̲` whenever `Rf_*E` is a
derived limit of `n ↦ Rf_*(E ⊗^𝐋_Λ (Λ/Iⁿ)̲)`**: the two towers are pro-isomorphic. -/
theorem isDerivedLimit_constantAdicTower_derivedPushforward_of_isDerivedLimit
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)))
    (L : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant J Λ).O)))
    (hL : IsDerivedLimit (RingedSite.constantAdicTower K Λ I E ⋙ constantDerivedPushforward Λ f)
      L) :
    IsDerivedLimit (RingedSite.constantAdicTower J Λ I ((constantDerivedPushforward Λ f).obj E))
      L := by
  obtain ⟨p⟩ := nonempty_proIso_constantAdicTower_derivedPushforward Λ f I E
  obtain ⟨M, hM⟩ := exists_isDerivedLimit
    (RingedSite.constantAdicTower J Λ I ((constantDerivedPushforward Λ f).obj E))
  obtain ⟨e⟩ := Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ M L hM hL p
  exact (RingedSite.isDerivedLimit_iff_of_iso e.symm).2 hM

/-- **`Rf_*` preserves derived completeness.** Let `Λ` be a Noetherian ring, `I ⊂ Λ` an ideal and
`f : Sh(𝒟) ⟶ Sh(𝒞)` a morphism of topoi. If `E` in `D(𝒟, Λ)` is derived complete along `IΛ̲`, so
is `Rf_*E` in `D(𝒞, Λ)`. -/
@[stacks 099N "(1)"]
theorem isDerivedComplete_constantDerivedPushforward
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)))
    (hE : RingedSite.IsDerivedComplete.{u, u, u, u} (RingedSite.constant K Λ)
      (RingedSite.constantIdealSheaf K Λ I) E) :
    RingedSite.IsDerivedComplete.{u, u, u, u} (RingedSite.constant J Λ)
      (RingedSite.constantIdealSheaf J Λ I) ((constantDerivedPushforward Λ f).obj E) := by
  rw [RingedSite.isDerivedComplete_iff_isDerivedLimit_constantAdicTower]
  exact isDerivedLimit_constantAdicTower_derivedPushforward_of_isDerivedLimit Λ f I E _
    (isDerivedLimit_map_constantDerivedPushforward Λ f _ E
      ((RingedSite.isDerivedComplete_iff_isDerivedLimit_constantAdicTower K Λ I E).1 hE))

/-- **`Rf_*` commutes with derived completion up to isomorphism**: `(Rf_*E)^∧ ≅ Rf_*(E^∧)` for
every `E` in `D(𝒟, Λ)`. Both sides are derived limits of pro-isomorphic towers. -/
theorem nonempty_iso_derivedCompletion_constantDerivedPushforward
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))) :
    Nonempty ((RingedSite.derivedCompletion (RingedSite.constant J Λ)
        (RingedSite.constantIdealSheaf J Λ I)).obj ((constantDerivedPushforward Λ f).obj E) ≅
      (constantDerivedPushforward Λ f).obj ((RingedSite.derivedCompletion
        (RingedSite.constant K Λ) (RingedSite.constantIdealSheaf K Λ I)).obj E)) := by
  have hC := RingedSite.isDerivedLimit_constantAdicTower_derivedCompletion J Λ I
    ((constantDerivedPushforward Λ f).obj E)
  have hD := isDerivedLimit_constantAdicTower_derivedPushforward_of_isDerivedLimit Λ f I E _
    (isDerivedLimit_map_constantDerivedPushforward Λ f _ _
      (RingedSite.isDerivedLimit_constantAdicTower_derivedCompletion K Λ I E))
  exact Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ _ _ hC hD
    (InverseSequence.ProIso.ofNatIso (Iso.refl _))

/-- `Rf_*` carries objects with zero derived completion to objects with zero derived
completion. -/
private theorem isZero_derivedCompletion_constantDerivedPushforward
    {E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))}
    (hE : IsZero ((RingedSite.derivedCompletion (RingedSite.constant K Λ)
      (RingedSite.constantIdealSheaf K Λ I)).obj E)) :
    IsZero ((RingedSite.derivedCompletion (RingedSite.constant J Λ)
      (RingedSite.constantIdealSheaf J Λ I)).obj ((constantDerivedPushforward Λ f).obj E)) := by
  obtain ⟨e⟩ := nonempty_iso_derivedCompletion_constantDerivedPushforward Λ f I E
  exact ((constantDerivedPushforward Λ f).map_isZero hE).of_iso e

/-- **`Rf_*` commutes with derived completion**: the canonical comparison
`(Rf_*E)^∧ ⟶ Rf_*(E^∧)`, the map produced from `Rf_*(E ⟶ E^∧)` by the universal property of
derived completion, is an isomorphism for every `E` in `D(𝒟, Λ)`.

The fibre `N` of `E ⟶ E^∧` and its shift have zero derived completion, so by
`MorphismOfTopoi.nonempty_iso_derivedCompletion_constantDerivedPushforward` the same holds for
`Rf_*N` and `Rf_*(N⟦1⟧)`; the distinguished triangle `Rf_*N ⟶ Rf_*E ⟶ Rf_*(E^∧) ⟶` then shows
that precomposition with `Rf_*(E ⟶ E^∧)` is bijective on maps into derived-complete objects,
which characterizes the derived completion. -/
theorem isIso_derivedCompletionComparisonApp_constantDerivedPushforward
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))) :
    IsIso (RingedSite.derivedCompletionComparisonApp (RingedSite.constantIdealSheaf K Λ I)
      (RingedSite.constantIdealSheaf J Λ I) (constantDerivedPushforward Λ f)
      (fun L hL => isDerivedComplete_constantDerivedPushforward Λ f I L hL) E) := by
  let R := constantDerivedPushforward Λ f
  let IC := RingedSite.constantIdealSheaf J Λ I
  let ID := RingedSite.constantIdealSheaf K Λ I
  obtain ⟨N, a, b, hT⟩ := distinguished_cocone_triangle₁
    ((RingedSite.derivedCompletionUnit (RingedSite.constant K Λ) ID).app E)
  have hN := fun {M} (hM : RingedSite.IsDerivedComplete.{u, u, u, u}
      (RingedSite.constant K Λ) ID M) =>
    RingedSite.eq_zero_of_distTriang_derivedCompletionUnit (RingedSite.constant K Λ) ID a b hT hM
  have hRZ₁ := isZero_derivedCompletion_constantDerivedPushforward Λ f I
    (RingedSite.isZero_derivedCompletion_of_forall_eq_zero _ _ fun M hM g => (hN hM).1 g)
  have hRZ₀ := isZero_derivedCompletion_constantDerivedPushforward Λ f I
    (RingedSite.isZero_derivedCompletion_of_forall_eq_zero _ _ fun M hM g => (hN hM).2 g)
  have hT' := R.map_distinguished _ hT
  have hrot := rot_of_distTriang _ hT'
  have hcomplete := isDerivedComplete_constantDerivedPushforward Λ f I _
    (RingedSite.isDerivedComplete_derivedCompletion_obj (RingedSite.constant K Λ) ID E)
  obtain ⟨θ, hθ⟩ := RingedSite.exists_iso_derivedCompletion_of_bijective_precomp
    (RingedSite.constant J Λ) IC hcomplete
    (R.map ((RingedSite.derivedCompletionUnit (RingedSite.constant K Λ) ID).app E))
    (fun M hM => by
      refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
      · rw [← sub_eq_zero]
        have h0 : R.map ((RingedSite.derivedCompletionUnit (RingedSite.constant K Λ) ID).app E) ≫
            (g₁ - g₂) = 0 := by
          rwa [Preadditive.comp_sub, sub_eq_zero]
        obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₂ _ hrot (g₁ - g₂) h0
        have h1 : ((R.commShiftIso (1 : ℤ)).app N).hom ≫ g' = 0 :=
          RingedSite.eq_zero_of_isZero_derivedCompletion _ _ hRZ₁ hM _
        rw [hg', (cancel_epi ((R.commShiftIso (1 : ℤ)).app N).hom).1 (h1.trans comp_zero.symm)]
        exact comp_zero
      · obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₂ _ hT' g
          (RingedSite.eq_zero_of_isZero_derivedCompletion _ _ hRZ₀ hM _)
        exact ⟨g', hg'.symm⟩)
  have hc : RingedSite.derivedCompletionComparisonApp ID IC R
      (fun L hL => isDerivedComplete_constantDerivedPushforward Λ f I L hL) E = θ.hom :=
    RingedSite.hom_ext_derivedCompletionUnit _ _ hcomplete <|
      (RingedSite.derivedCompletionUnit_comp_derivedCompletionComparisonApp ID IC R
        (fun L hL => isDerivedComplete_constantDerivedPushforward Λ f I L hL) E).trans hθ.symm
  rw [hc]
  infer_instance

end MorphismOfTopoi

end
