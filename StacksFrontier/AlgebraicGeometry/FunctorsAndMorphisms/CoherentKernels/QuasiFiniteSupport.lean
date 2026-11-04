module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSupport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.DirectSums
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-finiteness of the support of an exact kernel

Let `k` be a field, let `X` and `Y` be schemes of finite type over `k` with `X` separated, and
let `𝒦` be a coherent module on `X ×_k Y`. If the integral transform
`F_𝒦 = pr_{2,*}(𝒦 ⊗ pr₁^*(-))` is right exact and sends coherent modules to coherent modules,
then the scheme-theoretic support `Z` of `𝒦` is locally quasi-finite over `Y`. This is the
quasi-finiteness step of the proof of [Stacks, Tag 0FZN].

The argument is the one of the source, arranged so that it applies at every point of `Y`:

* for a closed point `x ∈ X` and a point `p ∈ Supp 𝒦` over `x`, the point `pr₂ p` lies in the
  support of `F_𝒦(𝒪_x)`, where `𝒪_x = 𝒪_X/𝔪_x`;
* for pairwise distinct closed points `x₁, …, xₙ` the map `𝒪_X ⟶ ⨁ᵢ 𝒪_{xᵢ}` is an epimorphism,
  so by right exactness the stalk of `F_𝒦(𝒪_X)` at `y` surjects jointly onto the nonzero stalks
  of the `F_𝒦(𝒪_{xᵢ})`; as `F_𝒦(𝒪_X)` is coherent, only finitely many closed points `x`
  contribute to a given `y`;
* over a closed point `y`, every point of the fibre of `Z ⟶ Y` closed in `X ×_k Y` lies over
  one of these finitely many `x`, and over each of them there are only finitely many points of
  `X ×_k Y` above `y`, because `κ(x)` is finite over `k`; the fibre is a Jacobson space, so it
  is finite;
* a morphism of finite type to a Jacobson scheme with finite fibres over the closed points is
  locally quasi-finite, because its non-quasi-finite locus is closed.

## Main results

* `AlgebraicGeometry.CoherentKernels.locallyQuasiFinite_schemeTheoreticSupport_of_exact`: the
  scheme-theoretic support of `𝒦` is locally quasi-finite over `Y`.
* `AlgebraicGeometry.CoherentKernels.locallyQuasiFinite_of_finite_preimage_closedPoints`:
  quasi-finiteness is detected on the fibres over closed points.
* `AlgebraicGeometry.CoherentKernels.finite_setOf_mem_supp_pointTestQcoh`: an additive right
  exact functor with `T(𝒪_X)` of finite type sees only finitely many closed points at a stalk.
* `AlgebraicGeometry.CoherentKernels.mem_supp_quasicoherentIntegralTransform_pointTestQcoh`:
  the support of `F_𝒦(𝒪_x)` contains the image of the part of `Supp 𝒦` over `x`.

## Implementation notes

The structure sheaf of a closed point is `AlgebraicGeometry.pointTestModule x 1`, the direct
image of the structure sheaf of the closed subscheme `{x}`. The support of `F_𝒦(𝒪_x)` is
computed without identifying `𝒦 ⊗ pr₁^*𝒪_x` with a direct image from `x ×_k Y`: that module is
supported in `pr₁⁻¹{x}`, whose part over an affine open `V ⊆ Y` lies in the affine open
`pr₁⁻¹U ∩ pr₂⁻¹V` for an affine open `U ∋ x`, and a section over that affine open extends by
zero to `pr₂⁻¹V`.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.CoherentKernels

/-! ### Counting quotients of a finite module over a local ring -/

/-- A finite module `M` over a local ring admits a bound `N` such that `M` cannot surject onto a
product of `n` nonzero modules once `n > N`: the joint map to `n` residue-field quotients makes
`κⁿ` a quotient of `M`, and `M` is spanned by `N` elements. -/
theorem exists_forall_le_of_surjective_pi (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ N : ℕ, ∀ (n : ℕ) (A : Fin n → Type v) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)],
      (∀ i, Nontrivial (A i)) → ∀ f : ∀ i, M →ₗ[R] A i,
      (∀ c : ∀ i, A i, ∃ m, ∀ i, f i m = c i) → n ≤ N := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := R) (M := M))
  refine ⟨S.card, fun n A _ _ hA f hf => ?_⟩
  have hsurj (i : Fin n) : Function.Surjective (f i) := fun a => by
    obtain ⟨m, hm⟩ := hf (Pi.single i a)
    exact ⟨m, (hm i).trans (Pi.single_eq_same i a)⟩
  have hfin (i : Fin n) : Module.Finite R (A i) := Module.Finite.of_surjective (f i) (hsurj i)
  choose χ hχ using fun i => Stacks.Support.exists_surjective_toResidueField (R := R) (M := A i)
  let ψ : M →ₗ[R] (Fin n → IsLocalRing.ResidueField R) :=
    LinearMap.pi fun i => (χ i).comp (f i)
  have hψ : Function.Surjective ψ := fun c => by
    choose a ha using fun i => hχ i (c i)
    obtain ⟨m, hm⟩ := hf a
    exact ⟨m, funext fun i => by simp [ψ, hm i, ha i]⟩
  have hspanR : Submodule.span R (ψ '' (S : Set M)) = ⊤ := by
    rw [← Submodule.map_span, hS, Submodule.map_top, LinearMap.range_eq_top.mpr hψ]
  have hspan : Submodule.span (IsLocalRing.ResidueField R)
      ((S.image ψ : Finset _) : Set (Fin n → IsLocalRing.ResidueField R)) = ⊤ := by
    rw [Finset.coe_image, eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span R (ψ '' (S : Set M)) := hspanR ▸ Submodule.mem_top
    exact Submodule.span_le_restrictScalars R (IsLocalRing.ResidueField R) _ hz
  calc n = Module.finrank (IsLocalRing.ResidueField R) (Fin n → IsLocalRing.ResidueField R) :=
        (Module.finrank_fin_fun _).symm
    _ = ((S.image ψ : Finset _) : Set (Fin n → IsLocalRing.ResidueField R)).finrank
          (IsLocalRing.ResidueField R) := by
        rw [Set.finrank, hspan, finrank_top]
    _ ≤ (S.image ψ).card := finrank_span_finset_le_card _
    _ ≤ S.card := Finset.card_image_le

/-! ### Maps into a finite biproduct, read through an additive functor -/

section Biproduct

variable {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] [DecidableEq ι]
  {B : ι → C} [HasBiproduct B] (F : C ⥤ AddCommGrpCat.{v}) [F.Additive]

/-- Every element of `F(⨁ Bᵢ)` is the sum of its components, read back through the inclusions. -/
theorem eq_sum_map_ι_map_π (w : F.obj (⨁ B)) :
    w = ∑ i, (F.map (biproduct.ι B i)).hom ((F.map (biproduct.π B i)).hom w) := by
  have h : (F.map (∑ j, biproduct.π B j ≫ biproduct.ι B j)).hom w =
      (F.map (𝟙 (⨁ B))).hom w := by
    rw [biproduct.total]
  have e : ((∑ j, F.map (biproduct.π B j) ≫ F.map (biproduct.ι B j))).hom =
      ∑ j, (F.map (biproduct.π B j) ≫ F.map (biproduct.ι B j)).hom :=
    map_sum AddCommGrpCat.homAddEquiv _ _
  simp only [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_comp, e, AddMonoidHom.finset_sum_apply, AddCommGrpCat.hom_comp,
    AddMonoidHom.comp_apply, AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at h
  exact h.symm

/-- If `F(g)` is surjective for `g : A ⟶ ⨁ Bᵢ`, then the components of `F(g)` are jointly
surjective onto `∏ F(Bᵢ)`. -/
theorem exists_forall_map_comp_π_eq {A : C} (g : A ⟶ ⨁ B)
    (hg : Function.Surjective (F.map g).hom) (c : ∀ i, F.obj (B i)) :
    ∃ a, ∀ i, (F.map (g ≫ biproduct.π B i)).hom a = c i := by
  obtain ⟨a, ha⟩ := hg (∑ i, (F.map (biproduct.ι B i)).hom (c i))
  refine ⟨a, fun j => ?_⟩
  rw [CategoryTheory.Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, ha,
    map_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp [← AddMonoidHom.comp_apply, ← AddCommGrpCat.hom_comp, ← CategoryTheory.Functor.map_comp]
  · intro i _ hij
    simp [← AddMonoidHom.comp_apply, ← AddCommGrpCat.hom_comp, ← CategoryTheory.Functor.map_comp,
      biproduct.ι_π_ne _ hij]

/-- A map into a finite biproduct is sent by `F` to a surjection when at most one summand has a
nonzero image under `F` and each component of the map is sent to a surjection. -/
theorem surjective_map_of_surjective_map_comp_π {A : C} (f : A ⟶ ⨁ B)
    (hsub : ∀ i j, i ≠ j → Subsingleton (F.obj (B i)) ∨ Subsingleton (F.obj (B j)))
    (hsurj : ∀ i, Function.Surjective (F.map (f ≫ biproduct.π B i)).hom) :
    Function.Surjective (F.map f).hom := by
  intro w
  have hzero (i : ι) (_ : Subsingleton (F.obj (B i))) (v : F.obj (⨁ B)) :
      (F.map (biproduct.ι B i)).hom ((F.map (biproduct.π B i)).hom v) = 0 := by
    rw [Subsingleton.elim ((F.map (biproduct.π B i)).hom v) 0, map_zero]
  by_cases h : ∃ j, Nontrivial (F.obj (B j))
  · obtain ⟨j, hj⟩ := h
    have key : ∀ v : F.obj (⨁ B),
        v = (F.map (biproduct.ι B j)).hom ((F.map (biproduct.π B j)).hom v) := fun v =>
      (eq_sum_map_ι_map_π F v).trans <| Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        fun i _ hij => hzero i
          ((hsub i j hij).resolve_right (not_subsingleton_iff_nontrivial.mpr hj)) v
    obtain ⟨a, ha⟩ := hsurj j ((F.map (biproduct.π B j)).hom w)
    refine ⟨a, ?_⟩
    rw [key ((F.map f).hom a), key w, ← ha, CategoryTheory.Functor.map_comp, AddCommGrpCat.hom_comp,
      AddMonoidHom.comp_apply]
  · push Not at h
    refine ⟨0, ?_⟩
    rw [map_zero, eq_sum_map_ι_map_π F w]
    exact (Finset.sum_eq_zero fun i _ => hzero i (h i) w).symm

end Biproduct

/-! ### Quasi-finiteness is detected on the fibres over closed points -/

/-- A morphism locally of finite type to a Jacobson scheme whose fibres over the closed points
are finite is locally quasi-finite: the points where it is not quasi-finite form a closed set,
which, if nonempty, contains a closed point; that point lies over a closed point, whose fibre is
a finite Jacobson space and hence discrete. -/
theorem locallyQuasiFinite_of_finite_preimage_closedPoints {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [LocallyOfFiniteType g] [JacobsonSpace Y]
    (h : ∀ y ∈ closedPoints Y, (g ⁻¹' {y}).Finite) : LocallyQuasiFinite g := by
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace g
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_unique fun z _ => ?_
  by_contra hz
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := {z | ¬ g.QuasiFiniteAt z}) ⟨z, hz⟩
    (g.isOpen_quasiFiniteAt.isClosed_compl).isLocallyClosed
  have hy := g.closePoints_subset_preimage_closedPoints hzc
  refine hz (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr ?_)
  have : Finite (g ⁻¹' {g z}) := (h _ hy).to_subtype
  have : Finite (g.fiber (g z)) := Finite.of_equiv _ (g.fiberHomeo (g z)).toEquiv.symm
  exact isOpen_discrete _

/-- Over a Jacobson base, a closed point `x` of a scheme locally of finite type has finite residue
field over the base, so the points of `X ×_S Y` lying over `x` and over a given `y` are finitely
many: they are among the points of the fibre over `y` of the finite morphism
`Spec κ(x) ×_S Y ⟶ Y`. -/
theorem finite_preimage_fst_inter_preimage_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [JacobsonSpace S] {x : X} (hx : IsClosed {x}) (y : Y) :
    (pullback.fst f g ⁻¹' {x} ∩ pullback.snd f g ⁻¹' {y}).Finite := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let m := pullback.map (X.fromSpecResidueField x ≫ f) g f g (X.fromSpecResidueField x) (𝟙 Y)
    (𝟙 S) (by simp) (by simp)
  refine (((pullback.snd (X.fromSpecResidueField x ≫ f) g).finite_preimage_singleton y).image
    m).subset ?_
  rintro p ⟨hp₁, hp₂⟩
  have hp : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ⟨pullback.snd f g p, by simp⟩⟩
    rw [Set.mem_preimage, hp₁, Scheme.range_fromSpecResidueField]
    exact Set.mem_singleton x
  obtain ⟨q, rfl⟩ := hp
  refine ⟨q, ?_, rfl⟩
  have : pullback.snd f g (m q) = pullback.snd (X.fromSpecResidueField x ≫ f) g q := by
    have e : m ≫ pullback.snd f g = pullback.snd (X.fromSpecResidueField x ≫ f) g :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    rw [← e]
    rfl
  rwa [Set.mem_preimage, ← this]

/-! ### Points of the support of a direct image -/

open TopologicalSpace Opposite in
/-- Let `f : P ⟶ Y` be a morphism of schemes and `N` an `𝒪_P`-module supported in a closed set
`C`. If an open `W ⊆ f⁻¹V` contains `C ∩ f⁻¹V` and carries a section of `N` with nonzero germ at
`p`, then `f p` lies in the support of `f_* N`: the section extends by zero to all of `f⁻¹V`. -/
theorem mem_supp_pushforward_of_germ_ne_zero {P Y : Scheme.{u}} (f : P ⟶ Y) (N : P.Modules)
    {C : Set P} (hC : IsClosed C) (hNC : SheafOfModules.supp N ⊆ C) {V : Y.Opens}
    {W : P.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (hCW : C ∩ (f ⁻¹ᵁ V : Set P) ⊆ W) {p : P} (hp : p ∈ W)
    (s : Γ(N, W)) (hs : N.presheaf.germ W p hp s ≠ 0) :
    f p ∈ SheafOfModules.supp ((Scheme.Modules.pushforward f).obj N) := by
  let O : Bool → P.Opens
    | true => W
    | false => (f ⁻¹ᵁ V) ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hOV (a : Bool) : O a ≤ f ⁻¹ᵁ V := by
    cases a
    · exact inf_le_left
    · exact hWV
  have hcov : f ⁻¹ᵁ V ≤ ⨆ a, O a := by
    intro z hz
    by_cases hzC : z ∈ C
    · exact (le_iSup O true) (hCW ⟨hzC, hz⟩)
    · exact (le_iSup O false) ⟨hz, hzC⟩
  let sO : ∀ a, N.presheaf.obj (op (O a))
    | true => s
    | false => 0
  have hcompat : TopCat.Presheaf.IsCompatible N.presheaf O sO := by
    intro a b
    by_cases hab : a = b
    · subst b
      rfl
    · have hsub : Subsingleton (N.presheaf.obj (op (O a ⊓ O b))) := by
        apply Stacks.Chow.subsingleton_sections_of_forall_notMem_supp N (O a ⊓ O b)
        intro z hz hzN
        cases a <;> cases b
        · exact hab rfl
        · exact hz.1.2 (hNC hzN)
        · exact hz.2.2 (hNC hzN)
        · exact hab rfl
      exact hsub.elim _ _
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf, Scheme.Modules.isSheaf N⟩ : TopCat.Sheaf Ab P)
    O (f ⁻¹ᵁ V) (fun a => homOfLE (hOV a)) hcov sO hcompat
  have hpV : f p ∈ V := hWV hp
  refine ⟨((Scheme.Modules.pushforward f).obj N).presheaf.germ V (f p) hpV t, fun h0 => hs ?_⟩
  have h3 : N.presheaf.map (homOfLE (hOV true)).op t = s := ht true
  have h2 : N.presheaf.germ W p hp s = Stacks.Chow.fibreStalkComparison f N (f p) p rfl
      (((Scheme.Modules.pushforward f).obj N).presheaf.germ V (f p) hpV t) := by
    rw [Stacks.Chow.fibreStalkComparison_germ, ← h3, N.presheaf.germ_res_apply]
  rw [h2, h0]
  exact map_zero (TopCat.Presheaf.stalkPushforward Ab.{u} f.base N.val.presheaf p).hom

open TopologicalSpace in
/-- On an affine open, a point of the support of a quasi-coherent module is detected by a
section over the whole open: every germ is a section divided by a function invertible near the
point. -/
theorem exists_germ_ne_zero_of_mem_supp {P : Scheme.{u}} (N : P.Modules) [N.IsQuasicoherent]
    {W : P.Opens} (hW : IsAffineOpen W) {p : P} (hp : p ∈ W)
    (hpN : p ∈ SheafOfModules.supp N) : ∃ s : Γ(N, W), N.presheaf.germ W p hp s ≠ 0 := by
  obtain ⟨m, hm⟩ := hpN
  let := Stacks.ModuleStalkSpecialization.stalkModule N p
  obtain ⟨s, c, hc, hcs⟩ := Stacks.ModuleStalkSpecialization.exists_germ_smul_eq_germ N hW hp m
  refine ⟨s, fun h0 => hm ?_⟩
  let : Algebra Γ(P, W) (P.presheaf.stalk p) := (P.presheaf.germ W p hp).hom.toAlgebra
  have : IsLocalization.AtPrime (P.presheaf.stalk p) (hW.primeIdealOf ⟨p, hp⟩).asIdeal :=
    hW.isLocalization_stalk ⟨p, hp⟩
  have hu : IsUnit (P.presheaf.germ W p hp c) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (P.presheaf.stalk p)
      (hW.primeIdealOf ⟨p, hp⟩).asIdeal c).mpr hc
  rw [h0] at hcs
  exact (hu.smul_eq_zero).mp hcs

/-- Over a local ring, the tensor product of two nonzero finite modules is nonzero: both
surject onto the residue field, and so the tensor product surjects onto `κ ⊗ κ ≠ 0`. -/
@[ega "0 1.7.5"]
theorem nontrivial_tensorProduct_of_finite {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R M]
    [Module.Finite R N] [Nontrivial M] [Nontrivial N] : Nontrivial (M ⊗[R] N) := by
  obtain ⟨χ, hχ⟩ := Stacks.Support.exists_surjective_toResidueField (R := R) (M := M)
  obtain ⟨ψ, hψ⟩ := Stacks.Support.exists_surjective_toResidueField (R := R) (M := N)
  have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] IsLocalRing.ResidueField R) :=
    RingHom.domain_nontrivial
      (Algebra.TensorProduct.lmul' R (S := IsLocalRing.ResidueField R)).toRingHom
  exact (TensorProduct.map_surjective hχ hψ).nontrivial

/-- A point `p` of the support of a finite type module `F` whose image lies in the support of a
finite type module `G` lies in the support of `F ⊗ f^* G`. -/
theorem mem_supp_tensorPullback {P X : Scheme.{u}} (f : P ⟶ X) (F : P.Modules) (G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] {p : P} (hpF : p ∈ SheafOfModules.supp F)
    (hpG : f p ∈ SheafOfModules.supp G) : p ∈ SheafOfModules.supp (tensorPullback f F G) := by
  have hpG' : p ∈ SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) := by
    rwa [Stacks.Modules.supp_pullback]
  have : Nontrivial (F.presheaf.stalk p) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F p).mp hpF
  have : Nontrivial (((Scheme.Modules.pullback f).obj G).presheaf.stalk p) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ p).mp hpG'
  have : Module.Finite (P.presheaf.stalk p) (F.presheaf.stalk p) :=
    SheafOfModules.finite_stalk P.sheaf F p
  have : Module.Finite (P.presheaf.stalk p)
      (((Scheme.Modules.pullback f).obj G).presheaf.stalk p) :=
    SheafOfModules.finite_stalk P.sheaf ((Scheme.Modules.pullback f).obj G) p
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk _ p).mpr ?_
  exact (tensorPullbackStalkEquiv f F G p).toEquiv.nontrivial_congr.mpr
    nontrivial_tensorProduct_of_finite

/-! ### The structure sheaves of closed points -/

section PointModules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The structure sheaf `𝒪_x = 𝒪_X/𝔪_x` of a point `x`, pushed forward to `X`, as a quasi-coherent
module. -/
def pointTestQcoh (x : X) : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ⟨pointTestModule x 1,
    @isQuasicoherent_of_isCoherent _ _ _ (pointTestModule x 1) (isCoherent_pointTestModule x 1)⟩

/-- The quotient map `𝒪_X ⟶ 𝒪_x` onto the structure sheaf of a point. -/
def toPointTestQcoh (x : X) :
    (⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩ :
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶ pointTestQcoh x :=
  ObjectProperty.homMk (Scheme.Modules.pushforwardUnitHom
    (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure ({x} : Set X)) ^ 1
      ).subschemeι)

/-- The stalks of quasi-coherent modules at a point, read as abelian groups. -/
abbrev qcohStalkFunctor (z : X) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  ObjectProperty.ι _ ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf z ⋙
    forget₂ _ AddCommGrpCat.{u}

/-- The stalk of `𝒪_x` vanishes away from the closed point `x`. -/
theorem subsingleton_qcohStalkFunctor_obj_pointTestQcoh (x : X) (hx : IsClosed {x}) {z : X}
    (hz : z ≠ x) : Subsingleton ((qcohStalkFunctor z).obj (pointTestQcoh x)) := by
  refine not_nontrivial_iff_subsingleton.mp fun h => hz ?_
  have hmem : z ∈ SheafOfModules.supp (pointTestModule x 1) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ z).mpr h
  rwa [supp_pointTestModule x hx one_ne_zero] at hmem

/-- The map `𝒪_X ⟶ 𝒪_x` is surjective on stalks. -/
theorem surjective_qcohStalkFunctor_map_toPointTestQcoh (x : X) (hx : IsClosed {x}) (z : X) :
    Function.Surjective ((qcohStalkFunctor z).map (toPointTestQcoh x)).hom := by
  by_cases hz : z = x
  · let J := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set X)) ^ 1
    have hxJ : x ∈ Set.range J.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ _ one_ne_zero,
        ← Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
      exact subset_closure rfl
    obtain ⟨c, hc⟩ := hxJ
    obtain rfl : z = J.subschemeι c := hz.trans hc.symm
    exact Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom J.subschemeι c
      J.subschemeι.isClosedEmbedding.isClosedMap
      (fun w hw => J.subschemeι.isClosedEmbedding.injective hw)
      (J.subschemeι.stalkMap_surjective c)
  · have := subsingleton_qcohStalkFunctor_obj_pointTestQcoh x hx hz
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- For pairwise distinct closed points `x₁, …, xₙ`, the map `𝒪_X ⟶ ⨁ᵢ 𝒪_{xᵢ}` is an
epimorphism of quasi-coherent modules: on the stalk at a point `z` at most one summand is
nonzero, and on that summand the map is the surjection `𝒪_{X,z} ⟶ κ(z)`. -/
theorem epi_biproductLift_toPointTestQcoh {n : ℕ} (x : Fin n → X) (hinj : Function.Injective x)
    (hx : ∀ i, IsClosed {x i}) :
    letI := CoherentModuleFunctors.hasFiniteBiproducts_quasicoherent X
    Epi (biproduct.lift fun i => toPointTestQcoh (x i)) := by
  let := CoherentModuleFunctors.hasFiniteBiproducts_quasicoherent X
  refine (ObjectProperty.ι _).epi_of_epi_map ?_
  rw [AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap]
  intro z
  refine surjective_map_of_surjective_map_comp_π (qcohStalkFunctor z) _ (fun i j hij => ?_)
    (fun i => ?_)
  · by_cases hzi : z = x i
    · exact .inr (subsingleton_qcohStalkFunctor_obj_pointTestQcoh (x j) (hx j)
        fun h => hij (hinj (hzi.symm.trans h)))
    · exact .inl (subsingleton_qcohStalkFunctor_obj_pointTestQcoh (x i) (hx i) hzi)
  · rw [biproduct.lift_π]
    exact surjective_qcohStalkFunctor_map_toPointTestQcoh (x i) (hx i) z

end PointModules

/-- Let `T : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be additive and right exact. If `A ⟶ ⨁ᵢ Bᵢ` is an
epimorphism, then on the stalks at any point of `Y` the maps `T(A) ⟶ T(Bᵢ)` are jointly
surjective onto `∏ᵢ T(Bᵢ)_y`. -/
theorem exists_stalkLinearMap_eq_of_epi {X Y : Scheme.{u}}
    [HasFiniteBiproducts (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]
    [HasFiniteBiproducts (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory]
    (T : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    [PreservesFiniteColimits T] [T.Additive] {n : ℕ}
    {A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    {B : Fin n → (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (π : ∀ i, A ⟶ B i) (hπ : Epi (biproduct.lift π)) (y : Y)
    (c : ∀ i, (Scheme.Modules.presheaf (X := Y) (T.obj (B i)).obj).stalk y) :
    ∃ m : (Scheme.Modules.presheaf (X := Y) (T.obj A).obj).stalk y,
      ∀ i, stalkLinearMap (T.obj A).obj (T.obj (B i)).obj (T.map (π i)).hom y m = c i := by
  let G : T.obj A ⟶ ⨁ (T.obj ∘ B) := biproduct.lift fun j => T.map (π j)
  have hG (i : Fin n) : G ≫ biproduct.π _ i = T.map (π i) := biproduct.lift_π _ _
  have : Epi G := by
    rw [show G = T.map (biproduct.lift π) ≫ (T.mapBiproduct B).hom from
      (biproduct.map_lift_mapBiprod T B π).symm]
    exact epi_comp _ _
  have := containsZero_isQuasicoherent Y
  have := ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
  have hepi : Epi ((ObjectProperty.ι _).map G) := (ObjectProperty.ι _).map_epi G
  rw [AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap] at hepi
  obtain ⟨m, hm⟩ := exists_forall_map_comp_π_eq (qcohStalkFunctor y) G (hepi y) c
  refine ⟨m, fun i => ?_⟩
  rw [← hG i]
  exact hm i

/-- **Only finitely many closed points contribute to a given stalk.** Let
`T : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be additive and right exact with `T(𝒪_X)` of finite type, and let
`y ∈ Y`. Then only finitely many closed points `x ∈ X` have `y ∈ Supp T(𝒪_x)`: for pairwise
distinct such points `x₁, …, xₙ`, the epimorphism `𝒪_X ⟶ ⨁ᵢ 𝒪_{xᵢ}` makes the nonzero stalks
`T(𝒪_{xᵢ})_y` jointly a quotient of the finite `𝒪_{Y,y}`-module `T(𝒪_X)_y`. -/
theorem finite_setOf_mem_supp_pointTestQcoh {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (T : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    [PreservesFiniteColimits T] [T.Additive]
    (hO : (T.obj ⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩).obj.IsFiniteType)
    (y : Y) :
    {x : X | IsClosed {x} ∧ y ∈ SheafOfModules.supp (T.obj (pointTestQcoh x)).obj}.Finite := by
  let := CoherentModuleFunctors.hasFiniteBiproducts_quasicoherent X
  let := CoherentModuleFunctors.hasFiniteBiproducts_quasicoherent Y
  let O : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X⟩
  let FO : Y.Modules := (T.obj O).obj
  have : Module.Finite (Y.presheaf.stalk y) (FO.presheaf.stalk y) :=
    @SheafOfModules.finite_stalk _ Y.sheaf (T.obj O).obj hO y
  obtain ⟨N, hN⟩ := exists_forall_le_of_surjective_pi (Y.presheaf.stalk y) (FO.presheaf.stalk y)
  by_contra hinf
  let e : Fin (N + 1) ↪ _ := Fin.valEmbedding.trans (Set.Infinite.natEmbedding _ hinf)
  let x : Fin (N + 1) → X := fun i => (e i : X)
  have hxinj : Function.Injective x := Subtype.val_injective.comp e.injective
  have hx (i : Fin (N + 1)) : IsClosed {x i} := (e i).2.1
  let A : Fin (N + 1) → Y.Modules := fun i => (T.obj (pointTestQcoh (x i))).obj
  have hle := hN (N + 1) (fun i => (A i).presheaf.stalk y)
    (fun i => (SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mp (e i).2.2)
    (fun i => stalkLinearMap (T.obj O).obj (T.obj (pointTestQcoh (x i))).obj
      (T.map (toPointTestQcoh (x i))).hom y)
    (exists_stalkLinearMap_eq_of_epi T (fun i => toPointTestQcoh (x i))
      (epi_biproductLift_toPointTestQcoh x hxinj hx) y)
  omega

/-! ### The points of the support of `T(𝒪_x)` -/

section IntegralTransform

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **The image of `𝒪_x` under the integral transform.** Let `p` be a point of the support of the
kernel `𝒦` lying over a closed point `x` of `X`. Then `pr₂ p` lies in the support of
`F_𝒦(𝒪_x) = pr_{2,*}(𝒦 ⊗ pr₁^* 𝒪_x)`: the module `𝒦 ⊗ pr₁^* 𝒪_x` is nonzero at `p` and supported
in `pr₁⁻¹{x}`, which over an affine open `V ∋ pr₂ p` lies in the affine open `pr₁⁻¹U ∩ pr₂⁻¹V`
for any affine open `U ∋ x`. -/
theorem mem_supp_quasicoherentIntegralTransform_pointTestQcoh [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] [IsLocallyNoetherian X.left]
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsCoherent] {x : X.left} (hx : IsClosed {x}) {p : ↥(pullback X.hom Y.hom)}
    (hpK : p ∈ SheafOfModules.supp K.obj) (hpx : pullback.fst X.hom Y.hom p = x) :
    pullback.snd X.hom Y.hom p ∈
      SheafOfModules.supp ((quasicoherentIntegralTransform k X Y K).obj (pointTestQcoh x)).obj := by
  let pr₁ := pullback.fst X.hom Y.hom
  let pr₂ := pullback.snd X.hom Y.hom
  have : K.obj.IsQuasicoherent := K.property
  have : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
  have hG : (pointTestModule x 1).IsCoherent := isCoherent_pointTestModule x 1
  have : (pointTestModule x 1).IsFiniteType := hG.isFiniteType
  have : (pointTestModule x 1).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  let N := tensorPullback pr₁ K.obj (pointTestModule x 1)
  have : N.IsQuasicoherent := Stacks.Chow.tensorPullback_isQuasicoherent pr₁ K.obj _
  refine (SheafOfModules.supp_eq_of_iso (X := Y.left)
    ((quasicoherentIntegralTransformData k X Y K).comparison.app (pointTestQcoh x))).symm ▸ ?_
  show pr₂ p ∈ SheafOfModules.supp ((Scheme.Modules.pushforward pr₂).obj N)
  have hNC : SheafOfModules.supp N ⊆ pr₁ ⁻¹' {x} := by
    refine (supp_tensorPullback_subset pr₁ K.obj (pointTestModule x 1)).trans fun z hz => ?_
    have := hz.2
    rwa [Set.mem_preimage, supp_pointTestModule x hx one_ne_zero] at this
  have hpN : p ∈ SheafOfModules.supp N := mem_supp_tensorPullback pr₁ K.obj _ hpK (by
    rw [hpx, supp_pointTestModule x hx one_ne_zero]
    exact Set.mem_singleton x)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (pr₂ p))
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top _
  let W := pr₁ ⁻¹ᵁ U ⊓ pr₂ ⁻¹ᵁ V
  have hW : IsAffineOpen W := isAffineOpen_inf_preimage X.hom Y.hom (S₀ := ⊤) le_top le_top
  have hpW : p ∈ W := ⟨show pr₁ p ∈ U from hpx ▸ hxU, hyV⟩
  obtain ⟨s, hs⟩ := exists_germ_ne_zero_of_mem_supp N hW hpW hpN
  refine mem_supp_pushforward_of_germ_ne_zero pr₂ N
    ((isClosed_singleton_iff_isClosedImmersion.mpr ?_).preimage pr₁.continuous) hNC
    (inf_le_right : W ≤ pr₂ ⁻¹ᵁ V) (fun z hz => ⟨?_, hz.2⟩) hpW s hs
  · exact isClosed_singleton_iff_isClosedImmersion.mp hx
  · show pr₁ z ∈ U
    rw [show pr₁ z = x from hz.1]
    exact hxU

/-- **Stacks Project, Tag 0FZN, the quasi-finiteness step.** Let `k` be a field, let `X` and `Y`
be schemes of finite type over `k` with `X` separated, and let `𝒦` be a coherent module on
`X ×_k Y` whose integral transform `F_𝒦` is right exact and sends coherent modules to coherent
modules. Then the scheme-theoretic support `Z` of `𝒦` is locally quasi-finite over `Y`.

By the Jacobson property it suffices that the fibres of `Z ⟶ Y` over closed points `y` be finite.
Every point of that fibre closed in `X ×_k Y` lies over a closed point `x` of `X` with
`y ∈ Supp F_𝒦(𝒪_x)`, and only finitely many closed points `x` do; the fibre is covered by the
finitely many finite sets of points of `X ×_k Y` over these `x` and over `y`. -/
theorem locallyQuasiFinite_schemeTheoreticSupport_of_exact
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    [K.obj.IsCoherent]
    (hT : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      letI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
      PreservesFiniteColimits (quasicoherentIntegralTransform k X Y K))
    (hcoh : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      letI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
      ∀ M, M.obj.IsCoherent → ((quasicoherentIntegralTransform k X Y K).obj M).obj.IsCoherent) :
    letI : K.obj.IsQuasicoherent := K.property
    letI : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
    LocallyQuasiFinite ((Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι ≫
      pullback.snd X.hom Y.hom) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : K.obj.IsQuasicoherent := K.property
  let : K.obj.IsFiniteType := ‹K.obj.IsCoherent›.isFiniteType
  let pr₁ := pullback.fst X.hom Y.hom
  let pr₂ := pullback.snd X.hom Y.hom
  let ι := (Scheme.Modules.schemeTheoreticSupport K.obj).subschemeι
  let T := quasicoherentIntegralTransform k X Y K
  have : PreservesFiniteColimits T := hT
  have : T.Additive := quasicoherentIntegralTransform_additive k X Y K
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have : JacobsonSpace ↥(pullback X.hom Y.hom) := LocallyOfFiniteType.jacobsonSpace (pr₁ ≫ X.hom)
  have hO := (hcoh ⟨SheafOfModules.unit X.left.ringCatSheaf,
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit).isFiniteType
  have hsuppK : SheafOfModules.supp K.obj = Set.range ι :=
    (Scheme.Modules.supp_eq_support_schemeTheoreticSupport K.obj).trans
      (Scheme.IdealSheafData.range_subschemeι _).symm
  refine locallyQuasiFinite_of_finite_preimage_closedPoints (ι ≫ pr₂) fun y hy => ?_
  have hC := finite_setOf_mem_supp_pointTestQcoh T hO y
  let C := {x : X.left | IsClosed {x} ∧
    y ∈ SheafOfModules.supp (T.obj (pointTestQcoh x)).obj}
  have hCc : IsClosed (pr₁ ⁻¹' C) := by
    refine IsClosed.preimage pr₁.continuous ?_
    rw [← Set.biUnion_of_singleton C]
    exact hC.isClosed_biUnion fun x hx => hx.1
  have hS : SheafOfModules.supp K.obj ∩ pr₂ ⁻¹' {y} ⊆
      ⋃ x ∈ C, pr₁ ⁻¹' {x} ∩ pr₂ ⁻¹' {y} := by
    intro p hp
    by_contra hpC
    have hp' : pr₁ p ∉ C := fun h => hpC (Set.mem_biUnion h ⟨rfl, hp.2⟩)
    obtain ⟨q, ⟨⟨hqK, hqy⟩, hqC⟩, hqc⟩ := nonempty_inter_closedPoints
      (Z := (SheafOfModules.supp K.obj ∩ pr₂ ⁻¹' {y}) ∩ (pr₁ ⁻¹' C)ᶜ) ⟨p, hp, hp'⟩
      (((hsuppK ▸ ι.isClosedEmbedding.isClosed_range).inter
        ((mem_closedPoints_iff.mp hy).preimage pr₂.continuous)).isLocallyClosed.inter
        hCc.isOpen_compl.isLocallyClosed)
    refine hqC ⟨pr₁.closePoints_subset_preimage_closedPoints hqc, ?_⟩
    rw [← show pr₂ q = y from hqy]
    exact mem_supp_quasicoherentIntegralTransform_pointTestQcoh k X Y K
      (pr₁.closePoints_subset_preimage_closedPoints hqc) hqK rfl
  have hSfin : (SheafOfModules.supp K.obj ∩ pr₂ ⁻¹' {y}).Finite :=
    (hC.biUnion fun x hx => finite_preimage_fst_inter_preimage_snd X.hom Y.hom hx.1 y).subset hS
  refine (hSfin.preimage ι.isClosedEmbedding.injective.injOn).subset fun z hz => ?_
  exact ⟨hsuppK ▸ Set.mem_range_self z, hz⟩

end IntegralTransform

end AlgebraicGeometry.CoherentKernels

end
