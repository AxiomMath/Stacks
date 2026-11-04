module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Operations preserving relative finite presentation

Relative finite presentation of a quasi-coherent module passes through a locally finitely
presented intermediate scheme, is inherited by the middle term of a short exact sequence whose
end terms have it, is inherited by the quotient term of a short exact sequence whose middle term
has it and whose sub-term is of finite type, and is inherited by each summand of a direct sum
that has it.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_comp` gives relative finite presentation over
  the composite morphism.
* `AlgebraicGeometry.isFinitelyPresentedRelative_of_shortExact` gives relative finite
  presentation of the middle term of a short exact sequence.
* `AlgebraicGeometry.isFinitelyPresentedRelative_of_shortExact_of_isFiniteType` gives relative
  finite presentation of the quotient term of a short exact sequence whose sub-term is of finite
  type.
* `AlgebraicGeometry.isFinitelyPresentedRelative_left_of_biprod` and
  `AlgebraicGeometry.isFinitelyPresentedRelative_right_of_biprod`: each summand inherits
  relative finite presentation.

## Implementation notes

Relative finite presentation is `AlgebraicGeometry.IsFinitelyPresentedRelative` for the
structure morphisms involved; the composition statement uses their categorical composite. The
locally finite type morphism and short exact sequence are packaged in
`AlgebraicGeometry.RelativeFinitePresentationExactSequenceSituation`, whose sequence objects
correspond to the left, middle, and right modules in the source.

The direct sum is the categorical biproduct in the category of sheaves of modules. The two
conclusions of tag 09TE are stated separately so they can be applied independently. Its locally
finite type and quasi-coherence assumptions are unnecessary for the relative finite-presentation
condition: at each affine open, sections of a finite biproduct split, and relative finite
presentation descends to each factor.

## References

* [Stacks Project, Tag 09TC](https://stacks.math.columbia.edu/tag/09TC)
* [Stacks Project, Tag 09TD](https://stacks.math.columbia.edu/tag/09TD)
* [Stacks Project, Tag 09TE](https://stacks.math.columbia.edu/tag/09TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 09TC.** Relative finite presentation of a quasi-coherent
module passes through a locally finitely presented intermediate scheme. -/
@[stacks 09TC]
theorem isFinitelyPresentedRelative_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [LocallyOfFinitePresentation g]
    (M : X.Modules) [M.IsQuasicoherent]
    (hM : IsFinitelyPresentedRelative f M) :
    IsFinitelyPresentedRelative (f ≫ g) M := by
  classical
  refine ⟨S.affineOpens, fun V : S.affineOpens => V.1, iSup_affineOpens_eq_top S,
    fun V => V.2, fun V => ?_⟩
  let I := {p : Y.affineOpens × X.affineOpens // p.1.1 ≤ g ⁻¹ᵁ V.1 ∧ p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  let U : I → X.Opens := fun i => i.1.2.1
  have hcover : (⨆ i, U i) = (f ≫ g) ⁻¹ᵁ V.1 := by
    apply le_antisymm
    · rw [Scheme.Hom.comp_preimage]
      exact iSup_le fun i => i.2.2.trans (f.preimage_mono i.2.1)
    · intro x hx
      rw [Scheme.Hom.comp_preimage] at hx
      obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hx (g ⁻¹ᵁ V.1).2
      obtain ⟨_, ⟨U₀ : X.Opens, hU₀, rfl⟩, hxU, hUW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hyW (f ⁻¹ᵁ W).2
      exact (le_iSup U (⟨(⟨W, hW⟩, ⟨U₀, hU₀⟩), hWV, hUW⟩ : I)) hxU
  refine ⟨I, U, hcover, fun i => i.1.2.2, fun i => ?_⟩
  let W : Y.affineOpens := i.1.1
  let U₀ : X.affineOpens := i.1.2
  have hWV : W.1 ≤ g ⁻¹ᵁ V.1 := i.2.1
  have hUW : U₀.1 ≤ f ⁻¹ᵁ W.1 := i.2.2
  have hUV : U₀.1 ≤ (f ≫ g) ⁻¹ᵁ V.1 := by
    rw [Scheme.Hom.comp_preimage]
    exact hUW.trans (f.preimage_mono hWV)
  let : Algebra Γ(S, V.1) Γ(Y, W.1) := (g.appLE V.1 W.1 hWV).hom.toAlgebra
  let : Algebra Γ(Y, W.1) Γ(X, U₀.1) := (f.appLE W.1 U₀.1 hUW).hom.toAlgebra
  let : Algebra Γ(S, V.1) Γ(X, U₀.1) := ((f ≫ g).appLE V.1 U₀.1 hUV).hom.toAlgebra
  have : IsScalarTower Γ(S, V.1) Γ(Y, W.1) Γ(X, U₀.1) :=
    .of_algebraMap_eq' (by simp only [RingHom.algebraMap_toAlgebra,
      ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE])
  let : Module Γ(Y, W.1) Γ(M, U₀.1) :=
    Module.compHom Γ(M, U₀.1) (algebraMap Γ(Y, W.1) Γ(X, U₀.1))
  have : IsScalarTower Γ(Y, W.1) Γ(X, U₀.1) Γ(M, U₀.1) := IsScalarTower.of_compHom _ _ _
  have : Algebra.FinitePresentation Γ(S, V.1) Γ(Y, W.1) :=
    g.finitePresentation_appLE V.2 W.2 hWV
  exact Module.finitePresentationRel_comp
    ((isFinitelyPresentedRelative_iff_affine f M).mp hM U₀.1 U₀.2 W.1 W.2 hUW)

private theorem epi_app_of_isAffineOpen {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  let f := hU.fromSpec
  let φ₂ := (Scheme.Modules.restrictFunctor f).map φ
  let P := SheafOfModules.isQuasicoherent (Spec (CommRingCat.of Γ(X, U))).ringCatSheaf
  let qM : P.FullSubcategory := ⟨M.restrict f, by infer_instance⟩
  let qN : P.FullSubcategory := ⟨N.restrict f, by infer_instance⟩
  let φq : qM ⟶ qN := ⟨φ₂⟩
  have : Epi φq := ⟨fun _ _ hab =>
    ObjectProperty.hom_ext _ ((cancel_epi φ₂).mp (congrArg (fun k => k.hom) hab))⟩
  have hEpiΓ :
      Epi ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of Γ(X, U))).inverse.map φq) :=
    inferInstance
  have hs₂ : Function.Surjective (φ₂.app ⊤) := by
    have h := (ModuleCat.epi_iff_surjective _).mp hEpiΓ
    change Function.Surjective (φ₂.app ⊤) at h
    exact h
  have hnat : φ₂.app ⊤ ≫ (N.restrictAppIso f ⊤).hom =
      (M.restrictAppIso f ⊤).hom ≫ φ.app (f ''ᵁ ⊤) := by
    ext x
    rfl
  rw [← show f ''ᵁ ⊤ = U by simp [f]]
  intro y
  obtain ⟨x, hx⟩ := hs₂ ((N.restrictAppIso f ⊤).inv y)
  refine ⟨(M.restrictAppIso f ⊤).hom x, ?_⟩
  have h := congrArg (fun q => q x) hnat
  change (N.restrictAppIso f ⊤).hom (φ₂.app ⊤ x) =
    φ.app (f ''ᵁ ⊤) ((M.restrictAppIso f ⊤).hom x) at h
  rw [← h, hx]
  simp

/-- Sections over an affine open of a short exact sequence of quasi-coherent modules form a short
exact sequence of modules. -/
private theorem shortExact_sections_exact
    (s : RelativeFinitePresentationExactSequenceSituation.{u}) (U : s.X.Opens)
    (hU : IsAffineOpen U) :
    ∃ (i : Γ(s.sequence.X₁, U) →ₗ[Γ(s.X, U)] Γ(s.sequence.X₂, U))
      (p : Γ(s.sequence.X₂, U) →ₗ[Γ(s.X, U)] Γ(s.sequence.X₃, U)),
      Function.Injective i ∧ Function.Surjective p ∧ LinearMap.range i = LinearMap.ker p := by
  let F := Scheme.Modules.toPresheafOfModules s.X ⋙
    PresheafOfModules.evaluation s.X.ringCatSheaf.obj (Opposite.op U)
  have hExactF : (s.sequence.map F).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ s.shortExact.fIsKernel F)
  have : Mono s.sequence.f := s.shortExact.mono_f
  have : Epi s.sequence.g := s.shortExact.epi_g
  refine ⟨(F.map s.sequence.f).hom, (F.map s.sequence.g).hom, ?_,
    epi_app_of_isAffineOpen s.sequence.g U hU, ?_⟩
  · have : Mono (F.map s.sequence.f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · show LinearMap.range ((s.sequence.map F).f).hom =
      LinearMap.ker ((s.sequence.map F).g).hom
    simpa [F, Scheme.Modules.toPresheafOfModules] using hExactF.moduleCat_range_eq_ker

/-- In a short exact sequence of quasi-coherent modules over a locally finite type
morphism, relative finite presentation of the two end terms implies that of the middle
term. -/
@[stacks 09TD "extension"]
theorem isFinitelyPresentedRelative_of_shortExact
    (s : RelativeFinitePresentationExactSequenceSituation.{u})
    (hleft : IsFinitelyPresentedRelative s.f s.sequence.X₁)
    (hright : IsFinitelyPresentedRelative s.f s.sequence.X₃) :
    IsFinitelyPresentedRelative s.f s.sequence.X₂ := by
  rw [isFinitelyPresentedRelative_iff_affine]
  intro U hU V hV hUV
  let : Algebra Γ(s.S, V) Γ(s.X, U) := (s.f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(s.S, V) Γ(s.X, U) := s.f.finiteType_appLE hV hU hUV
  have h₁ := ((isFinitelyPresentedRelative_iff_affine s.f s.sequence.X₁).mp
    hleft) U hU V hV hUV
  have h₃ := ((isFinitelyPresentedRelative_iff_affine s.f s.sequence.X₃).mp
    hright) U hU V hV hUV
  obtain ⟨i, p, hi, hp, hex⟩ := shortExact_sections_exact s U hU
  exact Module.finitePresentationRel_two_of_three i p hi hp hex h₁ h₃

/-- In a short exact sequence of quasi-coherent modules over a locally finite type
morphism whose left-hand term is of finite type, relative finite presentation of the middle
term implies that of the right-hand term. -/
@[stacks 09TD "quotient"]
theorem isFinitelyPresentedRelative_of_shortExact_of_isFiniteType
    (s : RelativeFinitePresentationExactSequenceSituation.{u})
    (hleft : s.sequence.X₁.IsFiniteType)
    (hmid : IsFinitelyPresentedRelative s.f s.sequence.X₂) :
    IsFinitelyPresentedRelative s.f s.sequence.X₃ := by
  rw [isFinitelyPresentedRelative_iff_affine]
  intro U hU V hV hUV
  let : Algebra Γ(s.S, V) Γ(s.X, U) := (s.f.appLE V U hUV).hom.toAlgebra
  have h₂ := ((isFinitelyPresentedRelative_iff_affine s.f s.sequence.X₂).mp
    hmid) U hU V hV hUV
  obtain ⟨i, p, -, hp, hex⟩ := shortExact_sections_exact s U hU
  exact Module.finitePresentationRel_of_surjective_of_finite i p hp hex
    (moduleFinite_sections_on_affine s.sequence.X₁ U hU) h₂

noncomputable section

private def sectionProdMap {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    (Γ(M ⊞ N, U) : Type _) →ₗ[Γ(X, U)] (Γ(M, U) : Type _) × Γ(N, U) :=
  { toFun := fun x => ((Limits.biprod.fst : M ⊞ N ⟶ M).app U x,
      (Limits.biprod.snd : M ⊞ N ⟶ N).app U x)
    map_add' := by simp
    map_smul' := by simp }

private def sectionProdInv {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    ((Γ(M, U) : Type _) × Γ(N, U)) →ₗ[Γ(X, U)] Γ(M ⊞ N, U) where
  toFun := fun p => (Limits.biprod.inl : M ⟶ M ⊞ N).app U p.1 +
    (Limits.biprod.inr : N ⟶ M ⊞ N).app U p.2
  map_add' := by
    intro a b
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro r p
    simp [smul_add]

private theorem sectionProdMap_inv {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : Γ(M ⊞ N, U)) : sectionProdInv M N U (sectionProdMap M N U x) = x :=
  congrArg (fun f : M ⊞ N ⟶ M ⊞ N => (f.app U).hom x)
    (Limits.biprod.total (X := M) (Y := N))

private theorem sectionProd_inv_map {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : (Γ(M, U) : Type _) × Γ(N, U)) : sectionProdMap M N U (sectionProdInv M N U x) = x := by
  apply Prod.ext
  · show (Limits.biprod.fst : M ⊞ N ⟶ M).app U
      ((Limits.biprod.inl : M ⟶ M ⊞ N).app U x.1 +
       (Limits.biprod.inr : N ⟶ M ⊞ N).app U x.2) = x.1
    rw [map_add]
    have h₁ : (Limits.biprod.fst : M ⊞ N ⟶ M).app U
          ((Limits.biprod.inl : M ⟶ M ⊞ N).app U x.1) = x.1 :=
      congrArg (fun f : M ⟶ M => (f.app U).hom x.1)
        (Limits.biprod.inl_fst (X := M) (Y := N))
    have h₂ : (Limits.biprod.fst : M ⊞ N ⟶ M).app U
          ((Limits.biprod.inr : N ⟶ M ⊞ N).app U x.2) = 0 :=
      congrArg (fun f : N ⟶ M => (f.app U).hom x.2)
        (Limits.biprod.inr_fst (X := M) (Y := N))
    rw [h₁, h₂]
    simp
  · show (Limits.biprod.snd : M ⊞ N ⟶ N).app U
      ((Limits.biprod.inl : M ⟶ M ⊞ N).app U x.1 +
       (Limits.biprod.inr : N ⟶ M ⊞ N).app U x.2) = x.2
    rw [map_add]
    have h₁ : (Limits.biprod.snd : M ⊞ N ⟶ N).app U
          ((Limits.biprod.inl : M ⟶ M ⊞ N).app U x.1) = 0 :=
      congrArg (fun f : M ⟶ N => (f.app U).hom x.1)
        (Limits.biprod.inl_snd (X := M) (Y := N))
    have h₂ : (Limits.biprod.snd : M ⊞ N ⟶ N).app U
          ((Limits.biprod.inr : N ⟶ M ⊞ N).app U x.2) = x.2 :=
      congrArg (fun f : N ⟶ N => (f.app U).hom x.2)
        (Limits.biprod.inr_snd (X := M) (Y := N))
    rw [h₁, h₂]
    simp

private def sectionProdEquiv {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    (Γ(M ⊞ N, U) : Type _) ≃ₗ[Γ(X, U)] ((Γ(M, U) : Type _) × Γ(N, U)) :=
  LinearEquiv.ofBijective (sectionProdMap M N U) ⟨
    fun x y h => by
      have := congrArg (sectionProdInv M N U) h
      simpa only [sectionProdMap_inv] using this,
    fun x => ⟨sectionProdInv M N U x, sectionProd_inv_map M N U x⟩⟩

end

private theorem relative_finitePresentation_prod_of_equiv
    {R A C M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup C] [Module A C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (e : C ≃ₗ[A] (M × N))
    (h : Module.FinitePresentationRel R A C) :
    Module.FinitePresentationRel R A (M × N) := by
  obtain ⟨n, α, hα, hfp⟩ := h
  let P := MvPolynomial (Fin n) R
  let : Algebra P A := α.toAlgebra
  let : Module P C := Module.compHom _ α.toRingHom
  let : Module P (M × N) := Module.compHom _ α.toRingHom
  have : IsScalarTower P A C := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower P A (M × N) := IsScalarTower.of_compHom _ _ _
  have : Module.FinitePresentation P C := hfp
  exact ⟨n, α, hα, .of_equiv (e.restrictScalars P)⟩

private theorem relative_of_biprod {X S : Scheme.{u}} (f : X ⟶ S) (M N : X.Modules)
    (h : IsFinitelyPresentedRelative f (M ⊞ N)) :
    IsFinitelyPresentedRelative f M ∧
      IsFinitelyPresentedRelative f N := by
  classical
  dsimp only [IsFinitelyPresentedRelative] at h ⊢
  obtain ⟨J, V, hV, hVa, h⟩ := h
  constructor
  all_goals
    refine ⟨J, V, hV, hVa, fun j => ?_⟩
    obtain ⟨I, U, hU, hUa, hUi⟩ := h j
    refine ⟨I, U, hU, hUa, fun i => ?_⟩
    let : Algebra Γ(S, V j) Γ(X, U i) :=
      (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.toAlgebra
  · exact (Module.finitePresentationRel_of_prod
      (relative_finitePresentation_prod_of_equiv (sectionProdEquiv M N (U i)) (hUi i))).1
  · exact (Module.finitePresentationRel_of_prod
      (relative_finitePresentation_prod_of_equiv (sectionProdEquiv M N (U i)) (hUi i))).2

/-- **Stacks Project, Tag 09TE.** The first summand of a relatively finitely presented direct
sum is relatively finitely presented. -/
@[stacks 09TE "first summand"]
theorem isFinitelyPresentedRelative_left_of_biprod
    {X S : Scheme.{u}} (f : X ⟶ S) (M N : X.Modules)
    (h : IsFinitelyPresentedRelative f (M ⊞ N)) :
    IsFinitelyPresentedRelative f M := (relative_of_biprod f M N h).1

/-- **Stacks Project, Tag 09TE.** The second summand of a relatively finitely presented direct
sum is relatively finitely presented. -/
@[stacks 09TE "second summand"]
theorem isFinitelyPresentedRelative_right_of_biprod
    {X S : Scheme.{u}} (f : X ⟶ S) (M N : X.Modules)
    (h : IsFinitelyPresentedRelative f (M ⊞ N)) :
    IsFinitelyPresentedRelative f N := (relative_of_biprod f M N h).2

end AlgebraicGeometry
