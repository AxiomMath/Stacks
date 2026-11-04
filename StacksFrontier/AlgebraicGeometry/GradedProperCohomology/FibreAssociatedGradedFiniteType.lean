module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraFiniteType
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullbackModule
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModulePieces
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Generation in degree zero of a pulled-back graded module of ideal-power multiples

Let `i : Z ⟶ X` be a morphism of schemes, let `ℐ` be a quasi-coherent sheaf of ideals on `X` and
let `F` be a quasi-coherent sheaf of `𝒪_X`-modules. `Stacks.Conormal.gradedPullbackModule i`
applied to `Stacks.Blowup.reesGradedModule ℐ F` is

`⨁ₙ i^*(ℐⁿF)` as a graded module over `i^*(⨁ₙ ℐⁿ)`,

the second of the three steps of
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedModule`. This file
proves that it is **generated in degree zero** and hence of finite type as soon as `F` is of
finite type over `𝒪_X`.

Both hypotheses of `SheafOfModules.GradedModule.generates_of_degreeZero` are discharged:

* the degree-zero piece is `i^*(ℐ⁰F) = i^*F` (`Stacks.Blowup.reesMultiple_zero`), and the
  pullbacks of a finite family generating `F` over an open `U` of `X` generate it over `i⁻¹U`;
* every homogeneous section of `⨁ₙ i^*(ℐⁿF)` is locally a finite sum of products of sections of
  the degree-zero piece with homogeneous sections of `i^*(⨁ₙ ℐⁿ)`, because that is already true
  upstairs (`Stacks.Blowup.exists_sum_smulSection_reesGradedModule`, which is
  `Stacks.Blowup.reesMultiple_le_iff` read pointwise) and the pullback of a product is the
  product of the pullbacks.

## Main results

* `Stacks.Conormal.exists_good_of_pullbackSpan` and
  `Stacks.Conormal.exists_sieve_good_of_pullbackSpan`: **the local spanning transfer.** A
  restriction-stable `Γ(Z, ·)`-submodule condition on the sections of a pullback `i^*N` of a
  quasi-coherent module, which holds locally around every point on the pullback of every section
  over an affine open of `X`, holds locally on every section of `i^*N`. This is
  `AlgebraicGeometry.span_pullbackSection_eq_top` packaged as the span induction that both
  generation statements below run, with the conclusion already in the covering-sieve shape
  `SheafOfModules.GradedModule.generates_of_degreeZero` consumes.
* `Stacks.Conormal.smulSection_pullbackSection`: the pulled-back action in a fixed total degree
  on pulled-back sections is the pullback of the action. This is
  `Stacks.Conormal.gradedPullbackModule_smul_pullbackSection` with the degree bookkeeping of
  `SheafOfModules.GradedModule.smulSection` performed and the open of `Z` arbitrary below the
  preimage.
* `Stacks.Conormal.generates_pullbackSection`: **the pullbacks of a finite family generating a
  quasi-coherent module over an open generate its inverse image over the preimage**, in the
  sectionwise sense of `PresheafOfModules.Generates`. This is the ungraded half of the statement
  and the sectionwise form of [Stacks, Tag 01B6] for one generating family.
* `Stacks.Blowup.generatesDegreeZeroPiece_gradedPullbackReesGradedModule`: the first hypothesis
  of `generates_of_degreeZero`, obtained from the previous item and
  `Stacks.Blowup.generatesDegreeZeroPiece_reesGradedModule`.
* `Stacks.Blowup.exists_sum_smulSection_gradedPullbackReesGradedModule`: the second one,
  **generation in degree zero**.
* `Stacks.Blowup.generates_gradedPullbackReesGradedModule` and
  `isFiniteType_gradedPullbackReesGradedModule`: **`⨁ₙ i^*(ℐⁿF)` is of finite type over
  `i^*(⨁ₙ ℐⁿ)`** as soon as `F` is of finite type and quasi-coherent.

## Implementation notes

Quasi-coherence of `F` is used only through
`AlgebraicGeometry.span_pullbackSection_eq_top`: the sections of a pullback over an affine open
are spanned by the pullbacks of the sections over an affine open above it only for a
quasi-coherent module. Finite type of `F` is `PresheafOfModules.IsFiniteType`, the repository's
sectionwise form of Stacks 03DL(5), exactly as in
`Stacks.Blowup.isFiniteType_reesGradedModule`; no coherence and no Noetherian hypothesis
appears, and nothing is assumed of `i`.

The statements are about the second step of the three-step construction of the fibre associated
graded module only — the pullback `i^*` — and not about the third, the restriction of scalars
along `Stacks.AssociatedGradedFibre.fibreAlgebraHom`. Nothing here imports
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreAssociatedGradedModule`, so the
transport of these results to `Stacks.AssociatedGradedFibre.fibreAssociatedGradedModule` — whose
pieces and whose degree-zero generation are the same objects, `restrictScalars` changing neither
— has to be stated in a file that does import it.

**Why the `Γ(M, U)` spelling of sections is used throughout.** The module structure of the
sections of a sheaf of modules over the functions, `Module Γ(X, U) Γ(M, U)`, is an instance
stated at the `AlgebraicGeometry.Scheme.Modules.presheaf` spelling of the sections; the
`SheafOfModules.val` spelling of the same type, which is what
`AlgebraicGeometry.Scheme.Modules.pullbackSection` and `PresheafOfModules.restrictₛₗ` produce, is
definitionally equal to it but is not found by instance search. Every span and every scalar
multiplication below is therefore written with `AlgebraicGeometry.pullbackSectionHom` and
`AlgebraicGeometry.Scheme.Modules.presheaf`, and the bridge to the `val` spelling is made at
`exact`, never inside a `rw`.

`AlgebraicGeometry.Scheme.Modules.pullbackSection` restricted to a smaller open is
`Stacks.Conormal.pullbackSection_restrict_target`, which already exists and is used as it
stands; no `restrictₛₗ`-spelled copy of it is introduced, the two spellings being
definitionally equal and the bridge made at `exact`.

`Stacks.Conormal.restrictₛₗ_trans` is the `AlgebraicGeometry.Scheme.Opens`-shape of
`SheafOfModules.GradedModule.restrictₛₗ_restrictₛₗ`, which does not apply on the nose because
`CategoryTheory.homOfLE h' ≫ homOfLE h` is not syntactically `homOfLE (h'.trans h)`; the two
arrows are identified by `Subsingleton.elim`, there being at most one arrow between two opens.

## References

* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Blowup

universe u

attribute [local instance] Stacks.Algebraization.sectionsModuleΓSheaf

namespace Stacks.Conormal

/-! ### Restriction calculus for pulled-back sections -/


variable {Z X : Scheme.{u}} (i : Z ⟶ X) (N : X.Modules)

/-- Restriction along two nested inclusions of opens is restriction along the composite, at the
`PresheafOfModules.restrictₛₗ` spelling the generation predicates use. -/
theorem restrictₛₗ_trans (P : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h : W₂ ≤ W₁) (h' : W₃ ≤ W₂)
    (t : Γ(P, W₁)) :
    P.val.restrictₛₗ (homOfLE h').op (P.val.restrictₛₗ (homOfLE h).op t) =
      P.val.restrictₛₗ (homOfLE (h'.trans h)).op t :=
  (PresheafOfModules.map_comp_apply P.val (homOfLE h).op (homOfLE h').op t).symm.trans
    (PresheafOfModules.congr_map_apply P.val (Subsingleton.elim _ _) t)

/-- Restriction along an arbitrary arrow of opens is restriction along the inclusion it is. -/
theorem restrictₛₗ_homOfLE (P : Z.Modules) {W₁ W₂ : Z.Opens} (g : W₂ ⟶ W₁) (t : Γ(P, W₁)) :
    P.val.restrictₛₗ g.op t = P.val.restrictₛₗ (homOfLE (leOfHom g)).op t :=
  PresheafOfModules.congr_map_apply P.val (Subsingleton.elim _ _) t

/-! ### The local spanning transfer -/

/-- **The local spanning transfer, pointwise.** Let `N` be a quasi-coherent module on `X` and let
`Good` be a condition on the sections of `i^*N` over the opens of `Z` below `i⁻¹U₀` which is
stable under restriction, contains zero and is closed under addition and under multiplication by
functions — that is, a sub-`Γ(Z, W)`-module of the sections over each such open `W`, compatible
with restriction. If, around every point, `Good` holds on the pullback of every section over an
affine open of `X` inside `U₀`, then around every point of an open `V` below `i⁻¹U₀` it holds on
every section of `i^*N` over `V`.

The sections of `i^*N` over an affine open `W` of `Z` are spanned over `Γ(Z, W)` by the
pullbacks of the sections over an affine open of `X` above it
(`AlgebraicGeometry.span_pullbackSection_eq_top`), so the statement is a span induction; the
point of the formulation is that the generators need only be *locally* good, which is why the
conclusion is local too and the inductive step for a sum intersects two opens. -/
theorem exists_good_of_pullbackSpan [N.IsQuasicoherent] (U₀ : X.Opens)
    (Good : ∀ W : Z.Opens, Γ((Scheme.Modules.pullback i).obj N, W) → Prop)
    (hres : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ → ∀ (W' : Z.Opens) (h : W' ≤ W)
      (t : Γ((Scheme.Modules.pullback i).obj N, W)), Good W t →
        Good W' (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op t))
    (hzero : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ → Good W 0)
    (hadd : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ →
      ∀ t t' : Γ((Scheme.Modules.pullback i).obj N, W),
        Good W t → Good W t' → Good W (t + t'))
    (hsmul : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ →
      ∀ (r : Γ(Z, W)) (t : Γ((Scheme.Modules.pullback i).obj N, W)), Good W t → Good W (r • t))
    (hgen : ∀ UA : X.affineOpens, (UA : X.Opens) ≤ U₀ → ∀ (WA : Z.affineOpens)
        (hWA : (WA : Z.Opens) ≤ i ⁻¹ᵁ (UA : X.Opens)) (a : Γ(N, (UA : X.Opens))) (z : Z),
        z ∈ (WA : Z.Opens) →
      ∃ (W' : Z.Opens) (h' : W' ≤ (WA : Z.Opens)), z ∈ W' ∧
        Good W' (Scheme.Modules.pullbackSection i N (UA : X.Opens) W' (h'.trans hWA) a))
    (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ U₀) (x : Γ((Scheme.Modules.pullback i).obj N, V))
    (z : Z) (hz : z ∈ V) :
    ∃ (W : Z.Opens) (h : W ≤ V), z ∈ W ∧
      Good W (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op x) := by
  obtain ⟨UA, hUAaff, hiz, hUA₀⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show i.base z ∈ U₀ from hV hz)
  obtain ⟨WA, hWAaff, hzWA, hWAle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show z ∈ V ⊓ i ⁻¹ᵁ UA from ⟨hz, hiz⟩)
  have hWAV : WA ≤ V := hWAle.trans inf_le_left
  have hWAU : WA ≤ i ⁻¹ᵁ UA := hWAle.trans inf_le_right
  have hWA₀ : WA ≤ i ⁻¹ᵁ U₀ := hWAV.trans hV
  have hspan : ((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE hWAV).op x ∈
      Submodule.span Γ(Z, WA)
        (Set.range fun a : Γ(N, UA) => pullbackSectionHom i N UA WA hWAU a) :=
    (span_pullbackSection_eq_top i N hUAaff hWAaff hWAU).ge Submodule.mem_top
  have key : ∀ t : Γ((Scheme.Modules.pullback i).obj N, WA),
      t ∈ Submodule.span Γ(Z, WA)
        (Set.range fun a : Γ(N, UA) => pullbackSectionHom i N UA WA hWAU a) →
      ∃ (W : Z.Opens) (h : W ≤ WA), z ∈ W ∧
        Good W (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op t) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t hmem =>
        obtain ⟨a, rfl⟩ := hmem
        obtain ⟨W', h', hzW', hG⟩ := hgen ⟨UA, hUAaff⟩ hUA₀ ⟨WA, hWAaff⟩ hWAU a z hzWA
        exact ⟨W', h', hzW',
          Eq.mpr (congrArg (Good W') (pullbackSection_restrict_target i N UA WA W' hWAU h' a)) hG⟩
    | zero =>
        exact ⟨WA, le_rfl, hzWA,
          Eq.mpr (congrArg (Good WA) (map_zero
            (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ
              (homOfLE (le_refl WA)).op))) (hzero WA hWA₀)⟩
    | add t t' _ _ iht iht' =>
        obtain ⟨W₁, h₁, hz₁, hG₁⟩ := iht
        obtain ⟨W₂, h₂, hz₂, hG₂⟩ := iht'
        refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hz₁, hz₂⟩, ?_⟩
        have res : ∀ (W : Z.Opens) (h : W ≤ WA) (hle : W₁ ⊓ W₂ ≤ W) (u),
            Good W (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op u) →
            Good (W₁ ⊓ W₂) (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ
              (homOfLE (hle.trans h)).op u) := fun W h hle u hG =>
          Eq.mp (congrArg (Good (W₁ ⊓ W₂)) (restrictₛₗ_trans
            ((Scheme.Modules.pullback i).obj N) h hle u)) (hres W (h.trans hWA₀) _ hle _ hG)
        have e₁ := res W₁ h₁ inf_le_left t hG₁
        have e₂ := res W₂ h₂ inf_le_right t' hG₂
        exact Eq.mpr (congrArg (Good (W₁ ⊓ W₂)) (map_add
          (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ
            (homOfLE (inf_le_left.trans h₁ : W₁ ⊓ W₂ ≤ WA)).op) t t'))
          (hadd _ ((inf_le_left.trans h₁).trans hWA₀) _ _ e₁ e₂)
    | smul r t _ iht =>
        obtain ⟨W, h, hzW, hG⟩ := iht
        exact ⟨W, h, hzW, Eq.mpr (congrArg (Good W) (map_smulₛₗ
          (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op) r t))
          (hsmul W (h.trans hWA₀) _ _ hG)⟩
  obtain ⟨W, h, hzW, hG⟩ := key _ hspan
  exact ⟨W, h.trans hWAV, hzW, Eq.mp (congrArg (Good W)
    (restrictₛₗ_trans ((Scheme.Modules.pullback i).obj N) hWAV h x)) hG⟩

/-- **The local spanning transfer, as a covering sieve.** The hypotheses are those of
`Stacks.Conormal.exists_good_of_pullbackSpan`; the conclusion is in the shape the two
hypotheses of `SheafOfModules.GradedModule.generates_of_degreeZero` are stated in.

The sieve is the set of opens on which `Good` holds of the restriction of the given section — a
sieve exactly because `Good` is stable under restriction — and it is covering because of the
pointwise statement. -/
theorem exists_sieve_good_of_pullbackSpan [N.IsQuasicoherent] (U₀ : X.Opens)
    (Good : ∀ W : Z.Opens, Γ((Scheme.Modules.pullback i).obj N, W) → Prop)
    (hres : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ → ∀ (W' : Z.Opens) (h : W' ≤ W)
      (t : Γ((Scheme.Modules.pullback i).obj N, W)), Good W t →
        Good W' (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ (homOfLE h).op t))
    (hzero : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ → Good W 0)
    (hadd : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ →
      ∀ t t' : Γ((Scheme.Modules.pullback i).obj N, W),
        Good W t → Good W t' → Good W (t + t'))
    (hsmul : ∀ W : Z.Opens, W ≤ i ⁻¹ᵁ U₀ →
      ∀ (r : Γ(Z, W)) (t : Γ((Scheme.Modules.pullback i).obj N, W)), Good W t → Good W (r • t))
    (hgen : ∀ UA : X.affineOpens, (UA : X.Opens) ≤ U₀ → ∀ (WA : Z.affineOpens)
        (hWA : (WA : Z.Opens) ≤ i ⁻¹ᵁ (UA : X.Opens)) (a : Γ(N, (UA : X.Opens))) (z : Z),
        z ∈ (WA : Z.Opens) →
      ∃ (W' : Z.Opens) (h' : W' ≤ (WA : Z.Opens)), z ∈ W' ∧
        Good W' (Scheme.Modules.pullbackSection i N (UA : X.Opens) W' (h'.trans hWA) a))
    (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ U₀) (x : Γ((Scheme.Modules.pullback i).obj N, V)) :
    ∃ S : Sieve V, S ∈ Opens.grothendieckTopology ↥Z V ∧
      ∀ (W : Z.Opens) (g : W ⟶ V), S g →
        Good W (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ g.op x) := by
  refine ⟨⟨fun W g => Good W (((Scheme.Modules.pullback i).obj N).val.restrictₛₗ g.op x), ?_⟩,
    ?_, fun W g hg => hg⟩
  · intro W W' g hg h
    have e := hres W ((leOfHom g).trans hV) W' (leOfHom h) _
      (Eq.mp (congrArg (Good W) (restrictₛₗ_homOfLE ((Scheme.Modules.pullback i).obj N) g x)) hg)
    refine Eq.mpr (congrArg (Good W') ?_) e
    exact (restrictₛₗ_homOfLE ((Scheme.Modules.pullback i).obj N) (h ≫ g) x).trans
      (restrictₛₗ_trans ((Scheme.Modules.pullback i).obj N)
        (leOfHom g) (leOfHom h) x).symm
  · rw [Opens.mem_grothendieckTopology]
    intro pt hpt
    obtain ⟨W, h, hptW, hG⟩ :=
      exists_good_of_pullbackSpan i N U₀ Good hres hzero hadd hsmul hgen V hV x pt hpt
    exact ⟨W, homOfLE h, hG, hptW⟩

/-! ### The pulled-back action in a fixed total degree -/

/-- Transporting a pulled-back section along an equality of degrees is pulling back the
transported section. -/
theorem castHom_pullbackSection (Nf : ℤ → X.Modules) {d e : ℤ} (h : d = e) (U : X.Opens)
    (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ U) (x : Γ(Nf d, U)) :
    SheafOfModules.castHom (fun m => (Scheme.Modules.pullback i).obj (Nf m)) h (op V)
        (Scheme.Modules.pullbackSection i (Nf d) U V hV x) =
      Scheme.Modules.pullbackSection i (Nf e) U V hV
        (SheafOfModules.castHom Nf h (op U) x) := by
  subst h
  rfl

variable {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **The pulled-back action in a fixed total degree on pulled-back sections** is the pullback of
the action: `Stacks.Conormal.gradedPullbackModule_smul_pullbackSection` with the degree
bookkeeping of `SheafOfModules.GradedModule.smulSection` performed, over an arbitrary open of
`Z` below the preimage rather than over the whole preimage. -/
theorem smulSection_pullbackSection (M : SheafOfModules.GradedModule.{u, u, u} A) (k d : ℤ)
    (U : X.Opens) (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ U) (x : Γ(M.piece d, U))
    (a : Γ(A.piece (k - d), U)) :
    (gradedPullbackModule i M).smulSection k
        (Scheme.Modules.pullbackSection i (M.piece d) U V hV x)
        (Scheme.Modules.pullbackSection i (A.piece (k - d)) U V hV a) =
      Scheme.Modules.pullbackSection i (M.piece k) U V hV (M.smulSection k x a) := by
  have hfull : (gradedPullbackModule i M).smulSection k
        (Scheme.Modules.pullbackSection i (M.piece d) U (i ⁻¹ᵁ U) le_rfl x)
        (Scheme.Modules.pullbackSection i (A.piece (k - d)) U (i ⁻¹ᵁ U) le_rfl a) =
      Scheme.Modules.pullbackSection i (M.piece k) U (i ⁻¹ᵁ U) le_rfl (M.smulSection k x a) :=
    (congrArg
        (SheafOfModules.castHom (fun m => (Scheme.Modules.pullback i).obj (M.piece m))
          (show d + (k - d) = k by omega) (op (i ⁻¹ᵁ U)))
        (gradedPullbackModule_smul_pullbackSection i M d (k - d) U x a)).trans
      (castHom_pullbackSection i M.piece (show d + (k - d) = k by omega) U (i ⁻¹ᵁ U) le_rfl
        (M.smul d (k - d) (op U) x a))
  rw [← pullbackSection_restrict_target i (M.piece d) U (i ⁻¹ᵁ U) V le_rfl hV x,
    ← pullbackSection_restrict_target i (A.piece (k - d)) U (i ⁻¹ᵁ U) V le_rfl hV a,
    ← pullbackSection_restrict_target i (M.piece k) U (i ⁻¹ᵁ U) V le_rfl hV (M.smulSection k x a)]
  exact (SheafOfModules.GradedModule.smulSection_restrictₛₗ (gradedPullbackModule i M) k
    (homOfLE hV).op _ _).symm.trans (congrArg _ hfull)


/-! ### Pullback of a generating family -/

/-- **The pullbacks of a finite family generating a quasi-coherent module `N` over an open `U` of
`X` generate `i^*N` over `i⁻¹U`**, sectionwise.

Over an affine open of `Z` sitting over an affine open of `X` inside `U`, the sections of `i^*N`
are spanned by the pullbacks of the sections of `N` over the latter
(`AlgebraicGeometry.span_pullbackSection_eq_top`), and each of those sections is in turn locally
a combination of the given family, which `Stacks.Conormal.exists_sieve_good_of_pullbackSpan`
composes. This is the sectionwise form of [Stacks, Tag 01B6] for one generating family. -/
theorem generates_pullbackSection [N.IsQuasicoherent] {U : X.Opens} {m : ℕ}
    (s : Fin m → Γ(N, U))
    (hs : PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) N.val s) :
    PresheafOfModules.Generates (Opens.grothendieckTopology ↥Z)
      ((Scheme.Modules.pullback i).obj N).val
      (fun a => Scheme.Modules.pullbackSection i N U (i ⁻¹ᵁ U) le_rfl (s a)) := by
  intro V fV y
  obtain ⟨S, hS, hGood⟩ := exists_sieve_good_of_pullbackSpan i N U
    (fun (W : Z.Opens) (t : Γ((Scheme.Modules.pullback i).obj N, W)) =>
      ∀ hW : W ≤ i ⁻¹ᵁ U, t ∈
        Submodule.span (M := Γ((Scheme.Modules.pullback i).obj N, W)) Γ(Z, W)
          (Set.range fun a : Fin m => pullbackSectionHom i N U W hW (s a)))
    (by
      intro W hW W' h t hG hW'
      refine Submodule.span_induction
        (p := fun u _ =>
            ((Scheme.Modules.pullback i).obj N).presheaf.map (homOfLE h).op u ∈
            Submodule.span (M := Γ((Scheme.Modules.pullback i).obj N, W')) Γ(Z, W')
              (Set.range fun a : Fin m => pullbackSectionHom i N U W' hW' (s a)))
        ?_ ?_ ?_ ?_ (hG hW)
      · rintro u ⟨a, rfl⟩
        exact Submodule.subset_span
          ⟨a, (pullbackSection_restrict_target i N U W W' hW h (s a)).symm⟩
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro u v _ _ hu hv
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      · intro r u _ hu
        rw [Scheme.Modules.map_smul]
        exact Submodule.smul_mem _ _ hu)
    (fun _ _ _ => Submodule.zero_mem _)
    (fun _ _ _ _ ht ht' hW => Submodule.add_mem _ (ht hW) (ht' hW))
    (fun _ _ r _ ht hW => Submodule.smul_mem _ r (ht hW))
    (by
      intro UA hUAU WA hWA a z hz
      obtain ⟨S₀, hS₀, hcomb⟩ := hs (UA : X.Opens) (homOfLE hUAU) a
      rw [Opens.mem_grothendieckTopology] at hS₀
      obtain ⟨U', g', hS₀g', hzU'⟩ := hS₀ (i.base z) (hWA hz)
      have hU'A : U' ≤ (UA : X.Opens) := leOfHom g'
      obtain ⟨c, hc⟩ := hcomb U' g' hS₀g'
      refine ⟨(WA : Z.Opens) ⊓ i ⁻¹ᵁ U', inf_le_left, ⟨hz, hzU'⟩, fun hW' => ?_⟩
      have hA := pullbackSection_restrict_source i N (UA : X.Opens) U' hU'A
        ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right a
      have hB : (∑ a' : Fin m, c a' •
            N.val.map (homOfLE (hU'A.trans hUAU)).op (s a')) =
          N.val.map (homOfLE hU'A).op a :=
        (Finset.sum_congr rfl fun a' _ => congrArg (fun w => c a' • w)
            (PresheafOfModules.congr_map_apply N.val (Subsingleton.elim
              (homOfLE (hU'A.trans hUAU)).op (g' ≫ homOfLE hUAU).op) (s a'))).trans
          (hc.trans (PresheafOfModules.congr_map_apply N.val
            (Subsingleton.elim g'.op (homOfLE hU'A).op) a))
      have hsum : Scheme.Modules.pullbackSection i N U'
            ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right
            (∑ a' : Fin m, c a' •
              N.val.map (homOfLE (hU'A.trans hUAU)).op (s a')) =
          ∑ a' : Fin m, i.appLE U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (c a') •
            pullbackSectionHom i N U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right
              (N.val.map (homOfLE (hU'A.trans hUAU)).op (s a')) :=
        (map_sum (ConcreteCategory.hom (pullbackSectionHom i N U'
          ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right)) _ Finset.univ).trans
          (Finset.sum_congr rfl fun a' _ => pullbackSectionHom_smul i N U'
            ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (c a') _)
      refine (Submodule.mem_span_range_iff_exists_fun
          Γ(Z, (WA : Z.Opens) ⊓ i ⁻¹ᵁ U')).2
        ⟨fun a' => i.appLE U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (c a'), ?_⟩
      refine Eq.trans (Finset.sum_congr rfl fun a' _ => congrArg
        (fun w => i.appLE U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (c a') • w)
        (pullbackSection_restrict_source i N U U' (hU'A.trans hUAU)
          ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (s a'))) ?_
      exact hsum.symm.trans ((congrArg (Scheme.Modules.pullbackSection i N U'
        ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right) hB).trans hA.symm))
    V (leOfHom fV) y
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(Z, W)).1
    (hGood W g hg ((leOfHom g).trans (leOfHom fV)))
  refine ⟨c, Eq.trans (Finset.sum_congr rfl fun a _ => ?_) hc⟩
  exact congrArg (fun w : Γ((Scheme.Modules.pullback i).obj N, W) => c a • w)
    ((restrictₛₗ_homOfLE ((Scheme.Modules.pullback i).obj N) (g ≫ fV) _).trans
      (pullbackSection_restrict_target i N U (i ⁻¹ᵁ U) W le_rfl (leOfHom (g ≫ fV)) (s a)))

end Stacks.Conormal

namespace Stacks.Blowup

open Stacks.Conormal (gradedPullbackModule gradedPullback)

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (I : X.IdealSheafData) (F : X.Modules)

/-! ### Generation of the degree-zero piece -/

/-- **The pullbacks of a generating family of `F` generate the degree-zero piece of
`⨁ₙ i^*(ℐⁿF)` over `i⁻¹U`.**

This is the first hypothesis of `SheafOfModules.GradedModule.generates_of_degreeZero`. The
degree-zero piece of `⨁ₙ ℐⁿF` is generated by a generating family of `F` read through
`Stacks.Blowup.reesSectionZero`, which is
`Stacks.Blowup.generatesDegreeZeroPiece_reesGradedModule`, and generation passes to the pullback
by `Stacks.Conormal.generates_pullbackSection`. -/
theorem generatesDegreeZeroPiece_gradedPullbackReesGradedModule [F.IsQuasicoherent]
    {U : X.Opens} {m : ℕ} (s : Fin m → Γ(F, U))
    (hs : PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) F.val s) :
    (gradedPullbackModule i (reesGradedModule I F)).GeneratesDegreeZeroPiece
      (fun a => Scheme.Modules.pullbackSection i ((reesGradedModule I F).piece 0) U
        (i ⁻¹ᵁ U) le_rfl (reesSectionZero I F (s a))) :=
  have : ((reesGradedModule I F).piece 0).IsQuasicoherent :=
    isQuasicoherent_piece_reesGradedModule I F 0
  Stacks.Conormal.generates_pullbackSection i ((reesGradedModule I F).piece 0)
    (fun a => reesSectionZero I F (s a)) (generatesDegreeZeroPiece_reesGradedModule I F s hs)

/-! ### Generation in degree zero -/

/-- **Generation in degree zero.** Every homogeneous section of `⨁ₙ i^*(ℐⁿF)` is, locally, a
finite sum of products of sections of the degree-zero piece with homogeneous sections of
`i^*(⨁ₙ ℐⁿ)`.

This is the second hypothesis of `SheafOfModules.GradedModule.generates_of_degreeZero`.
Upstairs on `X` it is `Stacks.Blowup.exists_sum_smulSection_reesGradedModule`, which is the
definition of `ℐᵏF` as the subsheaf generated by the products of sections of `ℐᵏ` with sections
of `F` (`Stacks.Blowup.reesMultiple_le_iff`), and it survives the pullback because the pullback
of a product is the product of the pullbacks
(`Stacks.Conormal.smulSection_pullbackSection`). -/
theorem exists_sum_smulSection_gradedPullbackReesGradedModule [F.IsQuasicoherent] (k : ℤ)
    (V : Z.Opens)
    (x : Γ((Scheme.Modules.pullback i).obj ((reesGradedModule I F).piece k), V)) :
    ∃ S : Sieve V, S ∈ Opens.grothendieckTopology ↥Z V ∧
      ∀ (W : Z.Opens) (g : W ⟶ V), S g →
        ∃ (q : ℕ)
          (y : Fin q →
            Γ((Scheme.Modules.pullback i).obj ((reesGradedModule I F).piece 0), W))
          (b : Fin q →
            Γ((Scheme.Modules.pullback i).obj ((reesGradedAlgebra I).piece (k - 0)), W)),
          ∑ jj, (gradedPullbackModule i (reesGradedModule I F)).smulSection k (y jj) (b jj) =
            ((Scheme.Modules.pullback i).obj
              ((reesGradedModule I F).piece k)).val.restrictₛₗ g.op x := by
  have : ((reesGradedModule I F).piece k).IsQuasicoherent :=
    isQuasicoherent_piece_reesGradedModule I F k
  refine Stacks.Conormal.exists_sieve_good_of_pullbackSpan i ((reesGradedModule I F).piece k) ⊤
    (fun W t => ∃ (q : ℕ)
      (y : Fin q → Γ((Scheme.Modules.pullback i).obj ((reesGradedModule I F).piece 0), W))
      (b : Fin q → Γ((Scheme.Modules.pullback i).obj ((reesGradedAlgebra I).piece (k - 0)), W)),
      ∑ jj, (gradedPullbackModule i (reesGradedModule I F)).smulSection k (y jj) (b jj) = t)
    (by
      rintro W _ W' h t ⟨q, y, b, hyb⟩
      refine ⟨q, fun jj => ((Scheme.Modules.pullback i).obj
          ((reesGradedModule I F).piece 0)).val.restrictₛₗ (homOfLE h).op (y jj),
        fun jj => ((Scheme.Modules.pullback i).obj
          ((reesGradedAlgebra I).piece (k - 0))).val.restrictₛₗ (homOfLE h).op (b jj), ?_⟩
      refine Eq.trans ?_ (congrArg
        (((Scheme.Modules.pullback i).obj
          ((reesGradedModule I F).piece k)).val.restrictₛₗ (homOfLE h).op) hyb)
      refine Eq.trans ?_ (map_sum
        (((Scheme.Modules.pullback i).obj
          ((reesGradedModule I F).piece k)).val.restrictₛₗ (homOfLE h).op) _ Finset.univ).symm
      exact Finset.sum_congr rfl fun jj _ =>
        (SheafOfModules.GradedModule.smulSection_restrictₛₗ
          (gradedPullbackModule i (reesGradedModule I F)) k (homOfLE h).op (y jj) (b jj)).symm)
    (fun _ _ => ⟨0, Fin.elim0, Fin.elim0, Fin.sum_univ_zero _⟩)
    (by
      rintro W _ t t' ⟨q₁, y₁, b₁, h₁⟩ ⟨q₂, y₂, b₂, h₂⟩
      refine ⟨q₁ + q₂, Fin.append y₁ y₂, Fin.append b₁ b₂, ?_⟩
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact congrArg₂ (· + ·) h₁ h₂)
    (by
      rintro W _ r t ⟨q, y, b, hyb⟩
      refine ⟨q, fun jj => r • y jj, b, ?_⟩
      refine Eq.trans (Finset.sum_congr rfl fun jj _ =>
        SheafOfModules.GradedModule.smulSection_smul_left
          (gradedPullbackModule i (reesGradedModule I F)) k r (y jj) (b jj)) ?_
      exact (Finset.smul_sum).symm.trans (congrArg (fun u => r • u) hyb))
    (by
      intro UA _ WA hWA a z hz
      obtain ⟨S₀, hS₀, hcomb⟩ :=
        exists_sum_smulSection_reesGradedModule I F k (UA : X.Opens) a
      rw [Opens.mem_grothendieckTopology] at hS₀
      obtain ⟨U', g', hS₀g', hzU'⟩ := hS₀ (i.base z) (hWA hz)
      have hU'A : U' ≤ (UA : X.Opens) := leOfHom g'
      obtain ⟨q, y, b, hyb⟩ := hcomb U' g' hS₀g'
      refine ⟨(WA : Z.Opens) ⊓ i ⁻¹ᵁ U', inf_le_left, ⟨hz, hzU'⟩, q,
        fun jj => Scheme.Modules.pullbackSection i ((reesGradedModule I F).piece 0) U'
          ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (y jj),
        fun jj => Scheme.Modules.pullbackSection i ((reesGradedAlgebra I).piece (k - 0)) U'
          ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (b jj), ?_⟩
      refine Eq.trans (Finset.sum_congr rfl fun jj _ =>
        Stacks.Conormal.smulSection_pullbackSection i (reesGradedModule I F) k 0 U'
          ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right (y jj) (b jj)) ?_
      refine Eq.trans (map_sum (ConcreteCategory.hom (pullbackSectionHom i
        ((reesGradedModule I F).piece k) U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right)) _
        Finset.univ).symm ?_
      refine Eq.trans (congrArg (Scheme.Modules.pullbackSection i
        ((reesGradedModule I F).piece k) U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right) hyb) ?_
      refine Eq.trans (congrArg (Scheme.Modules.pullbackSection i
          ((reesGradedModule I F).piece k) U' ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right)
        (Stacks.Conormal.restrictₛₗ_homOfLE ((reesGradedModule I F).piece k) g' a)) ?_
      exact (Stacks.Conormal.pullbackSection_restrict_source i
        ((reesGradedModule I F).piece k) (UA : X.Opens) U' hU'A
        ((WA : Z.Opens) ⊓ i ⁻¹ᵁ U') inf_le_right a).symm)
    V (le_top.trans (le_of_eq (Scheme.Hom.preimage_top i).symm)) x

/-! ### Finite type -/

/-- **Generators of `F` over an open `U` of `X` are generators of `⨁ₙ i^*(ℐⁿF)` as a graded
`i^*(⨁ₙ ℐⁿ)`-module over `i⁻¹U`**, all in degree zero. -/
theorem generates_gradedPullbackReesGradedModule [F.IsQuasicoherent]
    {U : X.Opens} {m : ℕ} (s : Fin m → Γ(F, U))
    (hs : PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) F.val s) :
    (gradedPullbackModule i (reesGradedModule I F)).Generates (fun _ : Fin m => (0 : ℤ))
      (fun a => Scheme.Modules.pullbackSection i ((reesGradedModule I F).piece 0) U
        (i ⁻¹ᵁ U) le_rfl (reesSectionZero I F (s a))) :=
  SheafOfModules.GradedModule.generates_of_degreeZero _ _
    (generatesDegreeZeroPiece_gradedPullbackReesGradedModule i I F s hs)
    (exists_sum_smulSection_gradedPullbackReesGradedModule i I F)

/-- **`⨁ₙ i^*(ℐⁿF)` is of finite type over `i^*(⨁ₙ ℐⁿ)` as soon as `F` is of finite type and
quasi-coherent over `𝒪_X`.**

The covering family is the family of preimages of a covering family of `X` carrying generators
of `F`, and on each member the pullbacks of those generators generate the whole graded module,
because it is generated in degree zero. Nothing is assumed of `i`. -/
theorem isFiniteType_gradedPullbackReesGradedModule [F.IsQuasicoherent]
    [hF : PresheafOfModules.IsFiniteType (Opens.grothendieckTopology ↥X) F.val] :
    (gradedPullbackModule i (reesGradedModule I F)).IsFiniteType where
  exists_generators := by
    obtain ⟨K, U, hU, hgen⟩ := hF.exists_generators
    refine ⟨ULift K, fun a => i ⁻¹ᵁ U a.down,
      RingedSpaceModuleAdjunction.coversTop_preimage i.toLRSHom.toShHom U hU, fun a => ?_⟩
    obtain ⟨n, s, hs⟩ := hgen a.down
    exact ⟨n, fun _ => 0, _, generates_gradedPullbackReesGradedModule i I F s hs⟩

end Stacks.Blowup

end
