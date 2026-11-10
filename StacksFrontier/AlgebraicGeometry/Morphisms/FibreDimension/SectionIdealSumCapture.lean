module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Defs
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Capturing a nonzero function by a sum of a quasi-coherent ideal sheaf

Let `f : X ⟶ S` be flat, locally of finite presentation and locally quasi-finite, and let `g` be
a nonzero global function on `X`. Then there are an open `U ⊆ S` and an open `V ⊆ f ⁻¹ U` on
which `g` stays nonzero, a quasi-coherent ideal sheaf `F ⊆ 𝒪_U`, and an injection of a finite
direct sum of `r > 0` copies of `F` into the direct image of `𝒪_V` whose image contains `g|_V`.

## Main results

* `AlgebraicGeometry.exists_open_injective_ideal_sum_with_section` produces the opens, the
  quasi-coherent subsheaf of the structure sheaf of `U`, and the monomorphism out of the finite
  sum whose global sections hit the restriction of `g`.

## Implementation notes

The ideal sheaf is presented as a submodule of the unit object, so the injection is a
monomorphism of sheaves of modules and the direct sum is a finite categorical coproduct. The
morphism between the open subschemes is `AlgebraicGeometry.Scheme.Hom.resLE`, for which the
commuting square is available by construction.

Shrinking `S` and `X` to affine opens makes the morphism separated and quasi-compact, so the
degree stratification of the base,
`AlgebraicGeometry.exists_quasiCompact_stratification_of_finiteLocallyFree_rank`, applies and
shows that each stratum of the bounded filtration
`AlgebraicGeometry.exists_closed_filtration_characterizing_finiteLocallyFree_rank` is compact.
The annihilator of the finitely generated ideal cutting out the closure of the stratum
containing the support of `g` is then the module whose base change along a flat map of affine
schemes provides the required finite sum.

## References

* [Stacks Project, Tag 082V](https://stacks.math.columbia.edu/tag/082V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u v u₁

namespace AlgebraicGeometry

/-- A nonzero global section of a scheme has a nonzero germ at some point. -/
private lemma exists_nonzero_germ {X : Scheme.{u}} (g : Γ(X, ⊤)) (hg : g ≠ 0) :
    ∃ x : X, X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) g ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  apply X.IsSheaf.section_ext
  intro x hx
  have hxg := h x
  have hxg' : (ConcreteCategory.hom (X.presheaf.germ ⊤ x hx)) g =
      (ConcreteCategory.hom (X.presheaf.germ ⊤ x hx)) 0 := by
    simpa using hxg
  obtain ⟨V, hxV, i, j, hij⟩ :=
    X.presheaf.germ_eq x hx (show x ∈ (⊤ : X.Opens) from trivial) g 0 hxg'
  refine ⟨V, le_top, hxV, ?_⟩
  have hi : i = homOfLE le_top := Subsingleton.elim _ _
  rw [← hi]
  simpa using hij

/-- A global section with a nonzero germ at a point of an open stays nonzero after restriction to
that open. -/
private lemma restrict_ne_zero_of_germ {X : Scheme.{u}} {g : Γ(X, ⊤)} {x : X}
    (hg : X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) g ≠ 0)
    (V : X.Opens) (hx : x ∈ V) (hV : V ≤ ⊤) :
    (X.presheaf.map (homOfLE hV).op) g ≠ 0 := by
  intro h
  apply hg
  have hres : (ConcreteCategory.hom (X.presheaf.germ V x hx))
      ((ConcreteCategory.hom (X.presheaf.map (homOfLE hV).op)) g) = 0 := by
    rw [h]
    exact map_zero _
  have hcomm := X.presheaf.germ_res_apply (homOfLE hV) x hx g
  change (ConcreteCategory.hom (X.presheaf.germ V x hx))
      ((ConcreteCategory.hom (X.presheaf.map (homOfLE hV).op)) g) =
    (ConcreteCategory.hom (X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial))) g at hcomm
  rw [hres] at hcomm
  exact hcomm.symm

/-- A global section with a nonzero germ at a point of an open stays nonzero when pulled back along
the inclusion of the corresponding open subscheme. -/
private lemma restrict_appTop_ne_zero_of_germ {X : Scheme.{u}} {g : Γ(X, ⊤)} {x : X}
    (hg : X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) g ≠ 0)
    (V : X.Opens) (hx : x ∈ V) : (V.ι.appTop).hom g ≠ 0 := by
  rw [Scheme.Opens.ι_appTop]
  apply restrict_ne_zero_of_germ hg
  simpa using hx

/-- If the pullback of a global section to an open subscheme has a nonzero germ at a point, the
section itself has a nonzero germ at the image of that point. -/
private lemma germ_nonzero_of_open_restriction {X : Scheme.{u}}
    (U : X.Opens) (g : Γ(X, ⊤)) (x : U.toScheme)
    (h : U.toScheme.presheaf.germ ⊤ x (by trivial) ((U.ι.appTop).hom g) ≠ 0) :
    X.presheaf.germ ⊤ (U.ι.base x) (by trivial) g ≠ 0 := by
  intro hz
  have hxU : U.ι.base x ∈ U.ι ''ᵁ ⊤ := by
    change ∃ y : U.toScheme, y ∈ (⊤ : U.toScheme.Opens) ∧
      U.ι.base y = U.ι.base x
    exact ⟨x, trivial, rfl⟩
  have hres : (X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base x) hxU).hom
      ((U.ι.appTop).hom g) = 0 := by
    have hcomm := X.presheaf.germ_res_apply
      (homOfLE (le_top : (U.ι ''ᵁ ⊤) ≤ ⊤)) (U.ι.base x) hxU g
    change (X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base x) hxU).hom
      ((U.ι.appTop).hom g) =
        (X.presheaf.germ ⊤ (U.ι.base x) (by trivial)).hom g at hcomm
    rw [hz] at hcomm
    exact hcomm
  have hiso : X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base x) hxU ≫ (U.stalkIso x).inv =
      U.toScheme.presheaf.germ ⊤ x (by trivial) :=
    Scheme.Opens.germ_stalkIso_inv U ⊤ x (by trivial)
  have hcomp :
      ((X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base x) hxU ≫
        (U.stalkIso x).inv).hom ((U.ι.appTop).hom g)) = 0 := by
    change (U.stalkIso x).inv.hom
      ((X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι.base x) hxU).hom ((U.ι.appTop).hom g)) = 0
    rw [hres]
    exact map_zero _
  have hval := congrArg (fun q => q.hom ((U.ι.appTop).hom g)) hiso
  exact h (hval.symm.trans hcomp)

/-- Around a point at which a global function has a nonzero germ there are affine opens `U` of the
target and `V ⊆ f ⁻¹ U` of the source, containing the point and its image, on which the function
stays nonzero. -/
private lemma exists_affine_restrictions {X S : Scheme.{u}} (f : X ⟶ S)
    {g : Γ(X, ⊤)} {x : X} (hg : X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) g ≠ 0) :
    ∃ (U : S.Opens) (V : X.Opens) (_hVU : V ≤ f ⁻¹ᵁ U),
      IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧ f.base x ∈ U ∧
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) g ≠ 0 := by
  obtain ⟨U, hUaff, hfU, hUsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f.base x) (U := ⊤) (by trivial)
  have hxpre : x ∈ f ⁻¹ᵁ U := by simpa using hfU
  obtain ⟨V, hVaff, hxV, hVsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ U) hxpre
  exact ⟨U, V, hVsub, hUaff, hVaff, hxV, hfU, restrict_ne_zero_of_germ hg V hxV le_top⟩

/-- The restriction of a morphism to affine opens of source and target is separated. -/
private lemma restrictedMap_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsSeparated (f.resLE U V hVU) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  infer_instance

/-- The restriction of a flat, locally finitely presented, locally quasi-finite morphism to an
affine open of the source has universally bounded fibres, the source being quasi-compact. -/
private lemma restrictedMap_hasBoundedFibers {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (hV : IsAffineOpen V) : HasUniversallyBoundedFibers (f.resLE U V hVU) := by
  let : IsAffine V.toScheme := hV
  let : CompactSpace V.toScheme := inferInstance
  exact hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace
    (f.resLE U V hVU)

/-- An increasing filtration indexed by `Fin (n + 2)` is monotone for the order on the index. -/
private lemma filtration_subset_of_le {α : Type*} {n : ℕ}
    (Z : Fin (n + 2) → Set α)
    (hmono : ∀ i : Fin (n + 1), Z i.castSucc ⊆ Z i.succ)
    {i j : Fin (n + 2)} (hij : i ≤ j) : Z i ⊆ Z j := by
  induction j using Fin.induction generalizing i with
  | zero =>
      have hi : i = 0 := Fin.le_zero_iff.mp hij
      subst i
      exact Set.Subset.rfl
  | succ j ih =>
      by_cases heq : i = j.succ
      · subst i
        exact Set.Subset.rfl
      · have hval := Fin.le_iff_val_le_val.mp hij
        have hne : i.val ≠ j.succ.val := by
          intro h
          exact heq (Fin.ext h)
        have hne' : i.val ≠ j.val + 1 := by simpa [Fin.val_succ] using hne
        have hval' : i.val ≤ j.val := by
          rw [Fin.val_succ] at hval
          omega
        have hle : i ≤ j.castSucc := Fin.le_iff_val_le_val.mpr (by
          simpa using hval')
        exact (ih hle).trans (hmono j)

/-- For a nonempty predicate there is a least step of an exhaustive increasing filtration
containing the image of its whole extension; at that step some point of the extension avoids the
previous step. -/
private lemma exists_min_filtration_level {α β : Type*} {n : ℕ}
    (Z : Fin (n + 2) → Set β) (hzero : Z 0 = ∅)
    (hlast : Z (Fin.last (n + 1)) = Set.univ)
    (f : α → β) (P : α → Prop) (hne : ∃ x, P x) :
    ∃ i : Fin (n + 1),
      (∀ x, P x → f x ∈ Z i.succ) ∧ ∃ x, P x ∧ f x ∉ Z i.castSucc := by
  classical
  let s : Finset (Fin (n + 2)) :=
    Finset.univ.filter fun k => ∀ x, P x → f x ∈ Z k
  have hs : s.Nonempty := by
    refine ⟨Fin.last (n + 1), ?_⟩
    simp [s, hlast]
  let k := s.min' hs
  have hk : ∀ x, P x → f x ∈ Z k := by
    simpa [s, k] using (Finset.min'_mem s hs)
  obtain ⟨x₀, hx₀⟩ := hne
  have hkpos : 0 < k.val := by
    by_contra hpos
    have hkval : k.val = 0 := by omega
    have hk0 : k = 0 := Fin.ext hkval
    have hxmem : f x₀ ∈ Z (0 : Fin (n + 2)) := by
      simpa [k, hk0] using hk x₀ hx₀
    rw [hzero] at hxmem
    simp at hxmem
  let i : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  have hisucc : i.succ = k := by
    apply Fin.ext
    dsimp [i]
    omega
  have hall : ∀ x, P x → f x ∈ Z i.succ := by
    intro x hx
    simpa [hisucc] using hk x hx
  have hsome : ∃ x, P x ∧ f x ∉ Z i.castSucc := by
    by_contra hn
    have hprev : ∀ x, P x → f x ∈ Z i.castSucc := by
      intro x hx
      by_contra hxnot
      exact hn ⟨x, hx, hxnot⟩
    have hi : i.castSucc ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprev
    have hmin := Finset.min'_le s (i.castSucc) hi
    have hle : k.val ≤ i.val := by
      have hval := Fin.le_iff_val_le_val.mp hmin
      simpa using hval
    have hisuccval : i.val + 1 = k.val := by
      have h := congrArg Fin.val hisucc
      simpa using h
    omega
  exact ⟨i, hall, hsome⟩

/-- Every point of an exhaustive increasing filtration indexed by `Fin (n + 2)` and starting at `∅`
lies in exactly one of its successive differences. -/
private lemma exists_filtration_stratum {α : Type*} {n : ℕ} (Z : Fin (n + 2) → Set α)
    (hzero : Z 0 = ∅) (hlast : Z (Fin.last (n + 1)) = Set.univ) (x : α) :
    ∃ i : Fin (n + 1), x ∈ Z i.succ \ Z i.castSucc := by
  obtain ⟨i, h₁, y, rfl, h₂⟩ := exists_min_filtration_level Z hzero hlast id (· = x) ⟨x, rfl⟩
  exact ⟨i, h₁ y rfl, h₂⟩

/-- A closed subset of a prime spectrum whose complement is retrocompact is the zero locus of a
finitely generated ideal. -/
private lemma exists_fg_ideal_of_retrocompact_complement {R : Type*} [CommRing R]
    (Z : Set (PrimeSpectrum R)) (hZ : IsClosed Z) (hretro : IsRetrocompact Zᶜ) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.zeroLocus (I : Set R) = Z := by
  obtain ⟨I, hIFG, hcomp⟩ :=
    PrimeSpectrum.isCompact_isOpen_iff_ideal.mp
      ⟨hretro.isCompact, isOpen_compl_iff.mpr hZ⟩
  refine ⟨I, hIFG, ?_⟩
  apply compl_injective
  ext x
  have hx := congrArg (fun A : Set (PrimeSpectrum R) => x ∈ A) hcomp
  simpa using hx

/-- A closed subset of an affine scheme whose complement is retrocompact is the zero locus of a
finitely generated ideal of global functions. -/
private lemma exists_fg_ideal_zeroLocus_eq_of_retrocompact_complement
    (X : Scheme.{u}) [IsAffine X] (Z : Set X)
    (hZ : IsClosed Z) (hretro : IsRetrocompact Zᶜ) :
    ∃ I : Ideal Γ(X, ⊤), I.FG ∧ X.zeroLocus (U := ⊤) I = Z := by
  obtain ⟨I₀, hI₀⟩ := (X.eq_zeroLocus_of_isClosed_of_isAffine Z).mp hZ
  have hcompact : IsCompact Zᶜ := by
    simpa using hretro isCompact_univ isOpen_univ
  have hspec : PrimeSpectrum.zeroLocus (I₀ : Set Γ(X, ⊤)) =
      X.isoSpec.hom.base '' Z := by
    rw [hI₀, X.isoSpec_image_zeroLocus]
  have hspecCompact : IsCompact
      (PrimeSpectrum.zeroLocus (I₀ : Set Γ(X, ⊤)))ᶜ := by
    have himage : X.isoSpec.hom.base '' Zᶜ =
        (X.isoSpec.hom.base '' Z)ᶜ :=
      X.isoSpec.hom.homeomorph.image_compl Z
    have hcompactImage := hcompact.image X.isoSpec.hom.continuous
    rw [himage] at hcompactImage
    rw [hspec]
    exact hcompactImage
  have hspecClosed : IsClosed
      (PrimeSpectrum.zeroLocus (I₀ : Set Γ(X, ⊤))) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hspecRetro : IsRetrocompact
      (PrimeSpectrum.zeroLocus (I₀ : Set Γ(X, ⊤)))ᶜ :=
    hspecCompact.isRetrocompact (isOpen_compl_iff.mpr hspecClosed)
  obtain ⟨I, hIFG, hI⟩ :=
    exists_fg_ideal_of_retrocompact_complement _ hspecClosed hspecRetro
  refine ⟨I, hIFG, ?_⟩
  rw [← X.isoSpec_inv_image_zeroLocus I, hI,
    X.isoSpec_inv_image_zeroLocus I₀, ← hI₀]

/-- **A closed subset of an affine scheme whose complement is retrocompact is the zero locus of a
finitely generated ideal of global functions.** Equivalently, such a `Z` is cut out by finitely
many global functions `g₁, …, gₛ ∈ Γ(X, 𝒪_X)`: take the generators of the ideal produced here.

On an affine scheme the complement of a closed subset is retrocompact exactly when it is
quasi-compact, since the whole space is quasi-compact; so this is also the statement that a
closed subset with quasi-compact complement is cut out by finitely many functions, which is the
hypothesis under which [Stacks, Tag 08EK] runs. A caller holding `IsCompact Zᶜ` supplies the
retrocompactness as `hcompact.isRetrocompact hZ.isOpen_compl`. -/
public alias exists_fg_ideal_zeroLocus_eq_of_isRetrocompact_compl :=
    exists_fg_ideal_zeroLocus_eq_of_retrocompact_complement

/-- The support of a cyclic module is the zero locus of its annihilator. -/
private lemma support_span_singleton_eq_zeroLocus_annihilator
    {R : Type*} [CommRing R] (b : R) :
    Module.support R (Submodule.span R ({b} : Set R)) =
      PrimeSpectrum.zeroLocus
        ((Submodule.span R ({b} : Set R)).annihilator : Set R) := by
  let M : Submodule R R := Submodule.span R ({b} : Set R)
  have hfg : M.FG := Submodule.fg_span (Set.finite_singleton b)
  let : Module.Finite R M := Module.Finite.iff_fg.mpr hfg
  rw [Module.support_eq_zeroLocus]

/-- If the zero locus of the annihilator of `b` lies in the zero locus of the ideal generated by
the image of `I`, then every element of `I` has a power annihilating `b`. -/
private lemma exists_pow_annihilates_of_zeroLocus_subset
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus
        ((Submodule.span B ({b} : Set B)).annihilator : Set B) ⊆
      PrimeSpectrum.zeroLocus (Ideal.map (algebraMap A B) I)) :
    ∀ a ∈ I, ∃ n : ℕ, (algebraMap A B a) ^ n * b = 0 := by
  have hrad : Ideal.map (algebraMap A B) I ≤
      ((Submodule.span B ({b} : Set B)).annihilator).radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hzero
  intro a ha
  have hmem : algebraMap A B a ∈ Ideal.map (algebraMap A B) I :=
    Ideal.mem_map_of_mem (algebraMap A B) ha
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hrad hmem)
  refine ⟨n, ?_⟩
  have hkill := (Submodule.mem_annihilator_span_singleton b _).mp hn
  simpa [smul_eq_mul] using hkill

/-- The same conclusion from the containment of the support of `B ∙ b` in the zero locus of the
ideal generated by the image of `I`. -/
private lemma exists_pow_annihilates_of_support_subset
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (I : Ideal A)
    (hsupp : Module.support B (Submodule.span B ({b} : Set B)) ⊆
      PrimeSpectrum.zeroLocus (Ideal.map (algebraMap A B) I : Set B)) :
    ∀ a ∈ I, ∃ n : ℕ, (algebraMap A B a) ^ n * b = 0 := by
  apply exists_pow_annihilates_of_zeroLocus_subset b I
  rwa [← support_span_singleton_eq_zeroLocus_annihilator]

/-- An element killed by the image of every element of an ideal annihilates the extended ideal. -/
private lemma mem_annihilator_map_of_mul_eq_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (b : B)
    (h : ∀ a ∈ I, algebraMap A B a * b = 0) :
    b ∈ Submodule.annihilator (Ideal.map (algebraMap A B) I) := by
  have hle : Ideal.map (algebraMap A B) I ≤ (Submodule.span B ({b} : Set B)).annihilator := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton]
    simpa [smul_eq_mul] using h a ha
  refine Submodule.mem_annihilator.mpr fun c hc => ?_
  have := (Submodule.mem_annihilator_span_singleton b c).mp (hle hc)
  simpa [smul_eq_mul, mul_comm] using this

/-- Replacing the generators of a finitely generated ideal by suitable powers gives a finitely
generated ideal with the same zero locus which annihilates `b` outright. -/
private lemma exists_fg_ideal_with_same_zeroLocus_annihilating
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (I : Ideal A) (hIFG : I.FG)
    (hkill : ∀ a ∈ I, ∃ n : ℕ, (algebraMap A B a) ^ n * b = 0) :
    ∃ J : Ideal A, J.FG ∧
      PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ a ∈ J, algebraMap A B a * b = 0 := by
  classical
  let e : A → ℕ := fun a =>
    if ha : a ∈ I then Classical.choose (hkill a ha) + 1 else 1
  have he (a : A) (ha : a ∈ I) : (algebraMap A B a) ^ e a * b = 0 := by
    have hn := Classical.choose_spec (hkill a ha)
    rw [show e a = Classical.choose (hkill a ha) + 1 by simp [e, ha]]
    rw [pow_succ']
    calc
      (algebraMap A B a * (algebraMap A B a) ^ Classical.choose (hkill a ha)) * b =
          algebraMap A B a * ((algebraMap A B a) ^ Classical.choose (hkill a ha) * b) := by ring
      _ = 0 := by rw [hn, mul_zero]
  let s := I.generators
  have hsfin : s.Finite := Submodule.FG.finite_generators hIFG
  have hsmem (a : A) (ha : a ∈ s) : a ∈ I :=
    Submodule.FG.generators_mem I ha
  let t : Set A := s.image (fun a => a ^ e a)
  have htfin : t.Finite := hsfin.image _
  let J : Ideal A := Ideal.span t
  have hJfg : J.FG := Submodule.fg_span htfin
  have hJleI : J ≤ I := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hepos : 0 < e x := by simp [e, hsmem x hx]
    exact Ideal.pow_mem_of_mem I (hsmem x hx) (e x) hepos
  let K : Ideal A := Ideal.comap (algebraMap A B)
      ((Submodule.span B ({b} : Set B)).annihilator)
  have hJleK : J ≤ K := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    change algebraMap A B (x ^ e x) ∈
      (Submodule.span B ({b} : Set B)).annihilator
    rw [Submodule.mem_annihilator_span_singleton]
    have hxkill := he x (hsmem x hx)
    rw [← map_pow] at hxkill
    simpa [smul_eq_mul] using hxkill
  have hIleRadJ : I ≤ J.radical := by
    rw [← Submodule.span_generators I]
    apply Ideal.span_le.mpr
    intro a ha
    change a ∈ J.radical
    rw [Ideal.mem_radical_iff]
    refine ⟨e a, ?_⟩
    exact Ideal.subset_span (Set.mem_image_of_mem _ ha)
  refine ⟨J, hJfg, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J I).mpr hIleRadJ
    · exact PrimeSpectrum.zeroLocus_anti_mono_ideal hJleI
  · intro a ha
    have hKa : a ∈ K := hJleK ha
    change algebraMap A B a ∈
      (Submodule.span B ({b} : Set B)).annihilator at hKa
    rw [Submodule.mem_annihilator_span_singleton] at hKa
    simpa [smul_eq_mul] using hKa

/-- The same ideal, produced from the containment of the support of `B ∙ b`. -/
private lemma exists_fg_ideal_with_same_zeroLocus_annihilating_of_support_subset
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (I : Ideal A) (hIFG : I.FG)
    (hsupp : Module.support B (Submodule.span B ({b} : Set B)) ⊆
      PrimeSpectrum.zeroLocus (Ideal.map (algebraMap A B) I : Set B)) :
    ∃ J : Ideal A, J.FG ∧
      PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ a ∈ J, algebraMap A B a * b = 0 :=
  exists_fg_ideal_with_same_zeroLocus_annihilating b I hIFG
    (exists_pow_annihilates_of_support_subset b I hsupp)

/-- On an affine source, if a global function has nonzero germs only over the zero locus of `I`,
then every element of `I` has a power annihilating it. -/
private lemma exists_pow_annihilates_of_germ_support_subset
    {X S : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    (b : Γ(X, ⊤)) (I : Ideal Γ(S, ⊤))
    (h : ∀ x : X,
      X.presheaf.germ ⊤ x (by trivial) b ≠ 0 →
        f.base x ∈ S.zeroLocus (U := ⊤) I) :
    ∀ a ∈ I, ∃ n : ℕ, (f.appTop.hom a) ^ n * b = 0 := by
  intro a ha
  let D := X.basicOpen (f.appTop.hom a)
  have hres : b |_ D = 0 := by
    apply TopCat.Presheaf.section_ext X.sheaf D
    intro x hx
    have hfx : f.base x ∈ S.basicOpen a := by
      have heq := congrArg (fun U : X.Opens => x ∈ U)
        (f.preimage_basicOpen_top a)
      exact heq.mpr hx
    have hnot : f.base x ∉ S.zeroLocus (U := ⊤) I := by
      intro hz
      exact ((S.mem_zeroLocus_iff I (f.base x)).mp hz a ha) hfx
    have hgzero : X.presheaf.germ ⊤ x (by trivial) b = 0 := by
      by_contra hn
      exact hnot (h x hn)
    have hcomm := X.presheaf.germ_res_apply
      (homOfLE (X.basicOpen_le (f.appTop.hom a))) x hx b
    change X.presheaf.germ D x hx (b |_ D) =
      X.presheaf.germ ⊤ x (by trivial) b at hcomm
    change X.presheaf.germ D x hx (b |_ D) =
      X.presheaf.germ D x hx 0
    rw [hcomm, hgzero, map_zero]
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X
    (isAffineOpen_top X) b (f.appTop.hom a) hres

/-- Multiplication of a ring element by each of the chosen generators of an ideal, as a linear map
into the functions on the set of generators. -/
private noncomputable def generatorMultiplicationMap {R : Type*} [CommRing R]
    (I : Ideal R) : R →ₗ[R] (↑I.generators → R) := by
  classical
  exact
    { toFun := fun a i => i.1 * a
      map_add' := by intro a b; funext i; simp [mul_add]
      map_smul' := by intro a b; funext i; simp [mul_comm, mul_left_comm] }

/-- An element killing every generator of an ideal annihilates the ideal. -/
private lemma generatorMultiplicationMap_ker_le_annihilator {R : Type*} [CommRing R]
    (I : Ideal R) (a : LinearMap.ker (generatorMultiplicationMap I)) :
    (a : R) ∈ Submodule.annihilator I := by
  rw [Submodule.mem_annihilator]
  intro x hx
  change (a : R) * x = 0
  rw [← Submodule.span_generators I] at hx
  have hgen : ∀ y ∈ I.generators, y * (a : R) = 0 := by
    intro y hy
    have hker : generatorMultiplicationMap I (a : R) = 0 := a.2
    have h := congrFun hker ⟨y, hy⟩
    simpa [generatorMultiplicationMap] using h
  induction hx using Submodule.span_induction with
  | mem y hy => simpa [mul_comm] using hgen y hy
  | zero => simp
  | add => simp_all [mul_add]
  | smul => simp_all [mul_comm, mul_left_comm, smul_eq_mul]

/-- An element annihilating an ideal kills every one of its generators. -/
private lemma annihilator_le_generatorMultiplicationMap_ker {R : Type*} [CommRing R]
    (I : Ideal R) (a : R) (ha : a ∈ Submodule.annihilator I) :
    a ∈ LinearMap.ker (generatorMultiplicationMap I) := by
  rw [Submodule.mem_annihilator] at ha
  change generatorMultiplicationMap I a = 0
  ext y
  have h := ha y.1 (Submodule.FG.generators_mem I y.2)
  simpa [generatorMultiplicationMap, smul_eq_mul, mul_comm] using h

/-- The kernel of multiplication by the generators of an ideal is its annihilator. -/
private noncomputable def generatorMultiplicationMapKerEquivAnnihilator
    {R : Type*} [CommRing R] (I : Ideal R) :
    LinearMap.ker (generatorMultiplicationMap I) ≃ₗ[R] Submodule.annihilator I := by
  classical
  refine
    { toFun := fun a => ⟨a.1, generatorMultiplicationMap_ker_le_annihilator I a⟩
      invFun := fun a => ⟨a.1, annihilator_le_generatorMultiplicationMap_ker I a.1 a.2⟩
      left_inv := by intro a; apply Subtype.ext; rfl
      right_inv := by intro a; apply Subtype.ext; rfl
      map_add' := by intro a b; apply Subtype.ext; rfl
      map_smul' := by intro c a; apply Subtype.ext; rfl }

/-- Multiplication by the images of the generators of an ideal of `A` in an `A`-algebra `B`. -/
private noncomputable def generatorMultiplicationMapBaseChange
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : B →ₗ[B] (↑I.generators → B) := by
  classical
  exact
    { toFun := fun b i => algebraMap A B i.1 * b
      map_add' := by intro b c; funext i; simp [mul_add]
      map_smul' := by intro b c; funext i; simp [mul_assoc, mul_comm] }

/-- Under the canonical identifications of `B ⊗[A] A` with `B` and of `B ⊗[A] (ι → A)` with
`ι → B`, multiplication by the generators base changes to multiplication by their images. -/
private lemma generatorMultiplicationMap_baseChange_commute
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (_hI : I.FG) :
    (generatorMultiplicationMapBaseChange I).comp
        (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap =
      TensorProduct.piScalarRightHom A B B (↑I.generators) ∘ₗ
        (TensorProduct.AlgebraTensorModule.lTensor B B (generatorMultiplicationMap I)) := by
  classical
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
      ext i
      simp [generatorMultiplicationMapBaseChange, generatorMultiplicationMap,
        TensorProduct.AlgebraTensorModule.rid_tmul,
        TensorProduct.piScalarRightHom_tmul, Algebra.smul_def,
        mul_comm, mul_left_comm]
  | add x y hx hy =>
      simp only [LinearMap.comp_apply, LinearMap.map_add, hx, hy]

/-- A commuting square of linear maps whose vertical arrows are equivalences identifies the kernels
of its horizontal arrows. -/
private noncomputable def linearEquivKerOfCommuting
    {R M N M' N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : eN.toLinearMap.comp f = g.comp eM.toLinearMap) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g := by
  refine
    { toFun := fun x => ⟨eM x.1, ?_⟩
      invFun := fun x => ⟨eM.symm x.1, ?_⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  · change g (eM x.1) = 0
    have hx := congrArg (fun q : M →ₗ[R] N' => q x.1) h
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
    calc
      g (eM x.1) = eN (f x.1) := hx.symm
      _ = 0 := by simp
  · change f (eM.symm x.1) = 0
    apply eN.injective
    have hx := congrArg (fun q : M →ₗ[R] N' => q (eM.symm x.1)) h
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
    simpa [x.2] using hx

/-- Over a flat algebra, the base change of the kernel of multiplication by the generators of an
ideal is the kernel of multiplication by their images. -/
private noncomputable def generatorMultiplicationMapKerBaseChangeEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : I.FG) :
    B ⊗[A] (LinearMap.ker (generatorMultiplicationMap I)) ≃ₗ[B]
      LinearMap.ker (generatorMultiplicationMapBaseChange (A := A) (B := B) I) := by
  classical
  letI : Finite (↑I.generators) := Submodule.FG.finite_generators hI
  letI : Fintype (↑I.generators) := Fintype.ofFinite _
  exact
    (LinearMap.tensorKerEquiv B B (generatorMultiplicationMap I)).trans
      (linearEquivKerOfCommuting
        (TensorProduct.AlgebraTensorModule.lTensor B B (generatorMultiplicationMap I))
        (generatorMultiplicationMapBaseChange (A := A) (B := B) I)
        (TensorProduct.AlgebraTensorModule.rid A B B)
        (TensorProduct.piScalarRight A B B (↑I.generators))
        (generatorMultiplicationMap_baseChange_commute I hI).symm)

/-- Over a flat algebra, an element of `B` annihilating the ideal generated by the image of `I`
comes from the base change of the annihilator of `I`. -/
private lemma exists_tensor_annihilator_preimage
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : I.FG) (b : B)
    (hb : b ∈ Submodule.annihilator (Ideal.map (algebraMap A B) I)) :
    ∃ t : B ⊗[A] Submodule.annihilator I,
      TensorProduct.AlgebraTensorModule.rid A B B
        ((Submodule.annihilator I).subtype.lTensor B t) = b := by
  classical
  let : Finite (↑I.generators) := Submodule.FG.finite_generators hI
  let : Fintype (↑I.generators) := Fintype.ofFinite _
  rw [Submodule.mem_annihilator] at hb
  have hker : b ∈ LinearMap.ker (generatorMultiplicationMapBaseChange I) := by
    change generatorMultiplicationMapBaseChange I b = 0
    ext i
    have h := hb (algebraMap A B i.1)
      (Ideal.mem_map_of_mem (algebraMap A B) (Submodule.FG.generators_mem I i.2))
    simpa [generatorMultiplicationMapBaseChange, mul_comm] using h
  let xb : LinearMap.ker (generatorMultiplicationMapBaseChange I) := ⟨b, hker⟩
  let x := (generatorMultiplicationMapKerBaseChangeEquiv I hI).symm xb
  let e := generatorMultiplicationMapKerEquivAnnihilator I
  let t := (TensorProduct.AlgebraTensorModule.lTensor B B e.toLinearMap) x
  refine ⟨t, ?_⟩
  have hval' : TensorProduct.AlgebraTensorModule.rid A B B
      ((LinearMap.tensorKer B B (generatorMultiplicationMap I) x :
        B ⊗[A] A)) = b := by
    simp [generatorMultiplicationMapKerBaseChangeEquiv, linearEquivKerOfCommuting, x, xb]
  have hmap : (Submodule.annihilator I).subtype.lTensor B t =
      (LinearMap.ker (generatorMultiplicationMap I)).subtype.lTensor B x := by
    change (Submodule.annihilator I).subtype.lTensor B
        ((e.toLinearMap.lTensor B) x) =
      (LinearMap.ker (generatorMultiplicationMap I)).subtype.lTensor B x
    induction x using TensorProduct.inductionOn with
    | tmul c y => simp [e, generatorMultiplicationMapKerEquivAnnihilator]
    | add x y hx hy => simp [hx, hy]
  rw [hmap]
  simpa [LinearMap.tensorKer_coe] using hval'

/-- The canonical map from the base change of the annihilator of an ideal to the algebra. -/
private noncomputable def tensorAnnihilatorSubtype
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : B ⊗[A] Submodule.annihilator I →ₗ[A] B :=
  (TensorProduct.rid A B).toLinearMap.comp
    ((Submodule.annihilator I).subtype.lTensor B)

/-- The canonical map from the base change of an annihilator is injective over a flat algebra. -/
private lemma tensorAnnihilatorSubtype_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) :
    Function.Injective (tensorAnnihilatorSubtype (A := A) (B := B) I) :=
  (TensorProduct.rid A B).injective.comp (Module.Flat.lTensor_preserves_injective_linearMap
    (Submodule.annihilator I).subtype (Submodule.annihilator I).injective_subtype)

/-- Over a flat algebra, the injective canonical map from the base change of the annihilator of `I`
hits any element of `B` annihilating the ideal generated by the image of `I`. -/
private lemma exists_injective_tensor_annihilator_preimage
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : I.FG) (b : B)
    (hb : b ∈ Submodule.annihilator (Ideal.map (algebraMap A B) I)) :
    ∃ t : B ⊗[A] Submodule.annihilator I,
      tensorAnnihilatorSubtype (A := A) (B := B) I t = b ∧
        Function.Injective (tensorAnnihilatorSubtype (A := A) (B := B) I) := by
  obtain ⟨t, ht⟩ := exists_tensor_annihilator_preimage I hI b hb
  exact ⟨t, ht, tensorAnnihilatorSubtype_injective (A := A) (B := B) I⟩

/-- An ideal acts by zero on its own annihilator. -/
private lemma ideal_smul_top_annihilator_eq_bot
    {A : Type*} [CommRing A] (I : Ideal A) :
    I • (⊤ : Submodule A (Submodule.annihilator I)) = ⊥ := by
  apply le_antisymm _ bot_le
  refine Submodule.smul_le.mpr fun a ha m _ => ?_
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have hm := (Submodule.mem_annihilator.mp m.property) a ha
  simpa [smul_eq_mul, mul_comm] using hm

/-- The annihilator of `I` is a module over `A ⧸ I`, so tensoring with `A ⧸ I` changes nothing. -/
private noncomputable def quotientTensorAnnihilatorEquiv
    {A : Type*} [CommRing A] (I : Ideal A) :
    (A ⧸ I) ⊗[A] Submodule.annihilator I ≃ₗ[A] Submodule.annihilator I :=
  TensorProduct.quotTensorEquivQuotSMul (Submodule.annihilator I) I ≪≫ₗ
    Submodule.quotEquivOfEqBot _ (ideal_smul_top_annihilator_eq_bot I)

/-- A trivialisation of `B ⧸ I B` as an `A ⧸ I`-module carries the base change of the annihilator
of `I` to the same number of copies of that annihilator. -/
private noncomputable def tensorAnnihilatorEquivPi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {ι : Type*} [Fintype ι]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₗ[A] (ι → A ⧸ I)) :
    B ⊗[A] Submodule.annihilator I ≃ₗ[A] (ι → Submodule.annihilator I) := by
  classical
  let q := quotientTensorAnnihilatorEquiv I
  let b := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv
    |>.restrictScalars A
  exact
    TensorProduct.congr (LinearEquiv.refl A B) q.symm ≪≫ₗ
    (TensorProduct.assoc A B (A ⧸ I) (Submodule.annihilator I)).symm ≪≫ₗ
    TensorProduct.congr (b.symm ≪≫ₗ e) (LinearEquiv.refl A _) ≪≫ₗ
    TensorProduct.piLeft A (Submodule.annihilator I) (fun _ : ι => A ⧸ I) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => q)

/-- A trivialisation of `B ⧸ I B` over `A ⧸ I` gives an injection of that many copies of the
annihilator of `I` into `B` whose image contains any prescribed annihilator of `I B`. -/
private lemma exists_injective_annihilator_pi_with_preimage
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : I.FG) {ι : Type*} [Finite ι]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₗ[A] (ι → A ⧸ I))
    (b : B) (hb : b ∈ Submodule.annihilator (Ideal.map (algebraMap A B) I)) :
    ∃ φ : (ι → Submodule.annihilator I) →ₗ[A] B,
      Function.Injective φ ∧ ∃ t, φ t = b := by
  let : Fintype ι := Fintype.ofFinite ι
  let E := tensorAnnihilatorEquivPi I e
  obtain ⟨t, ht, hinj⟩ := exists_injective_tensor_annihilator_preimage I hI b hb
  refine ⟨(tensorAnnihilatorSubtype I).comp E.symm.toLinearMap,
    hinj.comp E.symm.injective, E t, ?_⟩
  simpa using ht

/-- The same injection with index `Fin r`, where the rank `r` is positive as soon as the prescribed
element is nonzero. -/
private lemma exists_injective_annihilator_fin_with_preimage_positive
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I : Ideal A) (hI : I.FG) (r : ℕ)
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₗ[A] (Fin r → A ⧸ I))
    (b : B) (hb : b ∈ Submodule.annihilator (Ideal.map (algebraMap A B) I))
    (hbnz : b ≠ 0) :
    0 < r ∧ ∃ φ : (Fin r → Submodule.annihilator I) →ₗ[A] B,
      Function.Injective φ ∧ ∃ t, φ t = b := by
  classical
  obtain ⟨φ, hφ, t, ht⟩ :=
    exists_injective_annihilator_pi_with_preimage I hI e b hb
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    have ht0 : t = 0 := Subsingleton.elim _ _
    apply hbnz
    calc
      b = φ t := ht.symm
      _ = φ 0 := by rw [ht0]
      _ = 0 := map_zero φ
  exact ⟨hr, φ, hφ, t, ht⟩

/-- A basis of the localisation of `M` away from `a` trivialises any localisation of `M` away
from `a`. -/
private noncomputable def localBasisEquiv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) {S : Type*} [CommRing S] [Algebra R S] [IsLocalization.Away a S]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule (.powers a) f]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (Localization.Away a) (LocalizedModule (.powers a) M)) :
    N ≃ₗ[S] (ι → S) := by
  let e := (IsLocalizedModule.iso (.powers a) f).symm ≪≫ₗ
    b.equivFun.restrictScalars R ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : ι =>
      (IsLocalization.algEquiv (.powers a) (Localization.Away a) S).toLinearEquiv)
  exact e.extendScalarsOfIsLocalization (.powers a) S

/-- A basis of the localisation of `B ⧸ I B` away from the class of `a` trivialises the quotient of
the localisations of `A` and `B` away from `a`. -/
private noncomputable def quotientLocalBasis
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    (a : A) [IsLocalization.Away a A']
    [IsLocalization.Away (algebraMap A B a) B']
    (I : Ideal A) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (Localization.Away (Ideal.Quotient.mk I a))
      (LocalizedModule (.powers (Ideal.Quotient.mk I a))
        (B ⧸ Ideal.map (algebraMap A B) I))) :
    (B' ⧸ Ideal.map (algebraMap A' B') (I.map (algebraMap A A'))) ≃ₗ[A']
      (ι → A' ⧸ I.map (algebraMap A A')) := by
  let K := I.map (algebraMap A A')
  let L := I.map (algebraMap A B)
  have he : L.map (algebraMap B B') = K.map (algebraMap A' B') := by
    simp only [L, K, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let Q := A' ⧸ K
  let D := B' ⧸ K.map (algebraMap A' B')
  haveI : IsLocalization.Away (Ideal.Quotient.mk I a) Q := by
    simpa only [Algebra.algebraMapSubmonoid_powers, Ideal.Quotient.algebraMap_eq] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (.powers a)) Q)
  letI : Algebra (B ⧸ L) D :=
    (Ideal.quotientMap _ (algebraMap B B') (by rw [← he]; exact Ideal.le_comap_map)).toAlgebra
  haveI : IsLocalization.Away (algebraMap A B a |> Ideal.Quotient.mk L) D := by
    change IsLocalization (.powers (algebraMap B (B ⧸ L) (algebraMap A B a))) D
    rw [← Algebra.algebraMapSubmonoid_powers]
    apply IsLocalization.of_surjective (.powers (algebraMap A B a)) B'
      (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (K.map (algebraMap A' B'))) Ideal.Quotient.mk_surjective rfl
    simpa only [Ideal.mk_ker] using he.ge
  letI : Algebra (A ⧸ I) D := ((algebraMap Q D).comp (algebraMap (A ⧸ I) Q)).toAlgebra
  haveI : IsScalarTower (A ⧸ I) Q D := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (A ⧸ I) (B ⧸ L) D := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change Ideal.Quotient.mk _ (algebraMap A' B' (algebraMap A A' x)) =
      Ideal.Quotient.mk _ (algebraMap B B' (algebraMap A B x))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (B ⧸ L) (.powers (Ideal.Quotient.mk I a))) D := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact inferInstanceAs (IsLocalization.Away (Ideal.Quotient.mk L (algebraMap A B a)) D)
  exact (localBasisEquiv (Ideal.Quotient.mk I a)
    (IsScalarTower.toAlgHom (A ⧸ I) (B ⧸ L) D).toLinearMap b).restrictScalars A'

/-- Finite local freeness of a given rank transports along a linear equivalence. -/
private lemma locallyFreeRank_of_linearEquiv
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {r : ℕ} (e : M ≃ₗ[R] N)
    (h : Module.IsFiniteLocallyFreeOfRank R M r) :
    Module.IsFiniteLocallyFreeOfRank R N r := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine ⟨ι, f, hspan, ?_⟩
  intro i
  let l := LocalizedModule.map (Submonoid.powers (f i)) e.toLinearMap
  have hl : Function.Bijective l :=
    ⟨LocalizedModule.map_injective (Submonoid.powers (f i)) e.toLinearMap e.injective,
      LocalizedModule.map_surjective (Submonoid.powers (f i)) e.toLinearMap e.surjective⟩
  let E := LinearEquiv.ofBijective l hl
  obtain ⟨b⟩ := hbasis i
  exact ⟨b.map E⟩

/-- A monomorphism of sheaves of modules identifies its source with a submodule of its target,
namely the image subpresheaf. -/
private lemma exists_submodule_iso_of_mono
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Mono f] :
    ∃ P : N.Submodule, Nonempty (M ≅ P.toSheafOfModules) := by
  let P : N.val.Submodule := {
    obj U := LinearMap.range (f.val.app U).hom
    map {U V} g := by
      rintro _ ⟨x, rfl⟩
      exact ⟨M.val.map g x, PresheafOfModules.naturality_apply f.val g x⟩ }
  let a : M.val ⟶ P.toPresheafOfModules := {
    app U := ModuleCat.ofHom (f.val.app U).hom.rangeRestrict
    naturality {U V} g := by
      ext x
      exact Subtype.ext (PresheafOfModules.naturality_apply f.val g x) }
  have : Mono f.val := inferInstanceAs (Mono ((SheafOfModules.forget R).map f))
  have : IsIso a := by
    rw [← isIso_iff_of_reflects_iso a (PresheafOfModules.toPresheaf R.obj)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y h =>
      PresheafOfModules.injective_of_mono f.val U (congrArg Subtype.val h),
      by rintro ⟨y, x, hx⟩; exact ⟨x, Subtype.ext hx⟩⟩
  have hP : Presheaf.IsSheaf J P.toPresheafOfModules.presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf R.obj).mapIso (asIso a))).mp
      M.isSheaf
  let Q : N.Submodule := {
    toSubmodule := P
    isSheaf := by
      have hN : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{u}) :=
        (isSheaf_iff_isSheaf_of_type J _).mp
          (GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf)
      have hP' : Presieve.IsSheaf J P.toSubfunctor.toFunctor := by
        change Presieve.IsSheaf J (P.toPresheafOfModules.presheaf ⋙ forget AddCommGrpCat.{u})
        exact (isSheaf_iff_isSheaf_of_type J _).mp
          (GrothendieckTopology.HasSheafCompose.isSheaf _ hP)
      exact fun {_} => (P.toSubfunctor.isSheaf_iff hN).mp hP' _ }
  let b : M ⟶ Q.toSheafOfModules := ⟨a⟩
  have : IsIso b := by
    apply (isIso_iff_of_reflects_iso b (SheafOfModules.forget R)).mp
    change IsIso a
    infer_instance
  exact ⟨Q, ⟨asIso b⟩⟩

/-- A monomorphism out of a quasi-coherent sheaf of modules identifies its source with a
quasi-coherent submodule of its target. -/
private lemma exists_quasicoherent_submodule_iso_of_mono
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    [M.IsQuasicoherent] (f : M ⟶ N) [Mono f] :
    ∃ P : N.Submodule, P.toSheafOfModules.IsQuasicoherent ∧
      Nonempty (M ≅ P.toSheafOfModules) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_submodule_iso_of_mono f
  exact ⟨P, (SheafOfModules.isQuasicoherent R).prop_of_iso e inferInstance, ⟨e⟩⟩

/-- The associated sheaf functor preserves monomorphisms. -/
private lemma mono_tilde_map {R : CommRingCat.{u}} {M N : ModuleCat R} (i : M ⟶ N) [Mono i] :
    Mono (tilde.map i) :=
  let : (tilde.functor R).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape (tilde.functor R)
  (tilde.functor R).map_mono i

/-- A submodule of the ring itself gives, on the spectrum, a quasi-coherent ideal sheaf
isomorphic to the associated sheaf of that submodule. -/
private lemma exists_quasicoherent_ideal_of_module_mono
    (R : CommRingCat.{u}) (M : ModuleCat R)
    (i : M ⟶ ModuleCat.of R R) [Mono i] :
    ∃ F : (SheafOfModules.unit (Spec R).ringCatSheaf).Submodule,
      F.toSheafOfModules.IsQuasicoherent ∧
        Nonempty (tilde M ≅ F.toSheafOfModules) := by
  let j : tilde M ⟶ SheafOfModules.unit (Spec R).ringCatSheaf :=
    tilde.map i ≫ tildeSelf.hom
  have : Mono (tilde.map i) := mono_tilde_map i
  have : IsIso (tildeSelf (R := R)).hom :=
    (tildeSelf (R := R)).isIso_hom
  have : Mono (tildeSelf (R := R)).hom := IsIso.mono_of_iso _
  have hj : Mono j := by dsimp [j]; exact mono_comp _ _
  exact @exists_quasicoherent_submodule_iso_of_mono
    (Spec R).Opens _ _ _ _ _ (tilde M)
    (SheafOfModules.unit (Spec R).ringCatSheaf) _ j hj

/-- Finite local freeness of a given rank transports along an isomorphism of sheaves of modules. -/
private lemma finiteLocallyFreeOfRank_of_iso
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank N r := by
  obtain ⟨q, hq, hr⟩ :=
    (inferInstance :
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r
      ).exists_isFiniteLocallyFreeOfRankData
  let q' : N.LocalGeneratorsData := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i :=
      haveI : Epi ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom :=
        IsIso.epi_of_iso _
      (q.generators i).ofEpi ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom
  }
  refine ⟨q', ?_, ?_⟩
  · constructor
    intro i
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact let : IsIso (q.generators i).π := hq.isIso i
      IsIso.comp_isIso (f := (q.generators i).π)
        (h := ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom)
  · intro i
    exact hr i

/-- Isomorphic sheaves of modules are finite locally free of the same ranks. -/
private lemma finiteLocallyFreeOfRank_iff_of_iso
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank N r :=
  ⟨fun _ => finiteLocallyFreeOfRank_of_iso e r, fun _ => finiteLocallyFreeOfRank_of_iso e.symm r⟩

/-- Generating sections over an open which form a basis of cardinality `r` trivialise the module on
that open. -/
lemma local_rank_iso_of_generators {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (G : (M.over U).GeneratingSections) (r : ℕ)
    (hG : IsIso G.π) (hr : Nonempty (G.I ≃ Fin r)) :
    Nonempty ((M.restrict U.ι) ≅ SheafOfModules.free (ULift (Fin r))) := by
  let : IsIso G.π := hG
  let E := Scheme.Modules.overEquiv U
  let F := E.functor
  let : F.IsLeftAdjoint := Equivalence.isLeftAdjoint_functor E
  have : PreservesColimitsOfShape.{u, u} (Discrete G.I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit X.ringCatSheaf |>.over U) :=
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app
        (SheafOfModules.unit X.ringCatSheaf)).symm
  let e₁ := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F G.I this η
  let e₂ := F.mapIso (asIso G.π)
  let e₃ := (Scheme.Modules.overFunctorEquiv U).app M
  let e₄ : SheafOfModules.free G.I ≅ SheafOfModules.free (ULift (Fin r)) :=
    (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      ((Classical.choice hr).trans Equiv.ulift.symm).toIso
  exact ⟨e₃.symm ≪≫ e₂.symm ≪≫ e₁.symm ≪≫ e₄⟩

/-- The site-theoretic condition of being finite locally free of rank `r` gives a trivialisation by
free modules of rank `r` around every point. -/
public lemma modules_isFiniteLocallyFreeOfRank_of_sheafRank {X : Scheme.{u}}
    (M : X.Modules) (r : ℕ)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank M r := by
  intro x
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  have hcover := q.coversTop (⊤ : X.Opens)
  have hcover' : ∀ y ∈ (⊤ : X.Opens), ∃ V f,
      (Sieve.ofObjects q.X (⊤ : X.Opens)).arrows f ∧ y ∈ V :=
    (Opens.mem_grothendieckTopology (T := X)).mp hcover
  obtain ⟨V, f, hf, hxV⟩ := hcover' x (by simp)
  obtain ⟨i, ⟨g⟩⟩ := Sieve.mem_ofObjects_iff q.X f |>.mp hf
  refine ⟨q.X i, g.le hxV, ?_⟩
  let : IsIso (q.generators i).π := hfree.isIso i
  obtain ⟨e⟩ := hrank i
  simpa using local_rank_iso_of_generators M (q.generators i) r inferInstance ⟨e⟩

/-- On the spectrum of a ring, a sheaf of modules finite locally free of rank `r` has global
sections finite locally free of rank `r`. -/
private lemma module_isFiniteLocallyFreeOfRank_of_sheafRank_spec
    (R : CommRingCat.{u}) (M : (Spec R).Modules) (r : ℕ)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Module.IsFiniteLocallyFreeOfRank R
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) r := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  let : SheafOfModules.IsLocallyFree.{u, u, u} M := by
    obtain ⟨q, hq, -⟩ :=
      (inferInstance :
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M
        ).exists_isFiniteLocallyFreeData
    exact SheafOfModules.IsLocallyFree.mk (M := M) ⟨q, hq⟩
  let : M.IsQuasicoherent := by
    let hlf := (inferInstance : SheafOfModules.IsLocallyFree.{u, u, u} M)
    let q := hlf.exists_isLocallyFreeData.choose
    let : q.IsLocallyFreeData := hlf.exists_isLocallyFreeData.choose_spec
    exact q.quasiCoherentData.isQuasicoherent
  let : IsIso M.fromTildeΓ := inferInstance
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  let e : tilde N ≅ M := asIso M.fromTildeΓ
  have hM := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules M r inferInstance
  have hN : (tilde N).IsFiniteLocallyFreeOfRank r := by
    intro x
    obtain ⟨U, hx, ⟨eU⟩⟩ := hM x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e) ≪≫ eU⟩⟩
  exact (tilde_isFiniteLocallyFreeOfRank_iff R N r).mp hN

/-- Base changing along a morphism into an open of the target has the same rank as base changing
along its composite with the inclusion of that open. -/
private lemma finiteLocallyFreeOfRank_baseChange_open_iff
    {X S T : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (g : T ⟶ U) (r : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g (f ∣_ U)) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst (g ≫ U.ι) f) r := by
  have H : IsPullback
      (pullback.snd g (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι)
      (pullback.fst g (f ∣_ U)) f (g ≫ U.ι) :=
    (IsPullback.of_hasPullback g (f ∣_ U)).flip.paste_horiz
      (isPullback_morphismRestrict f U).flip
  let e := H.flip.isoPullback
  have he : e.hom ≫ pullback.fst (g ≫ U.ι) f =
      pullback.fst g (f ∣_ U) := H.flip.isoPullback_hom_fst
  rw [← he]
  exact (rank_comp_iso e _ r).symm

/-- Two filtrations of the target that both characterise the degree of the finite locally free
base changes of `f` have the same stratum of degree `r`: both conditions are tested on the
morphism from the residue field at a point, whose range is that point. -/
private lemma sdiff_eq_sdiff_of_rank_characterizations {X S : Scheme.{u}} (f : X ⟶ S)
    {n : ℕ} (Z : Fin (n + 2) → Set S)
    (hchar : ∀ (r : Fin (n + 1)) (T : Scheme.{u}) (g : T ⟶ S),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f g) r.val ↔
        Set.range g.base ⊆ Z r.succ \ Z r.castSucc)
    (Z' : ℕ → Set S)
    (hchar' : ∀ (r : ℕ) (T : Scheme.{u}) (g : T ⟶ S),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
        Set.range g.base ⊆ Z' (r + 1) \ Z' r)
    (r : Fin (n + 1)) :
    Z r.succ \ Z r.castSucc = Z' (r.val + 1) \ Z' r.val := by
  ext s
  let g := S.fromSpecResidueField s
  have hsingle : Set.range g.base = {s} := Scheme.range_fromSpecResidueField s
  have h₁ := hchar r (Spec (S.residueField s)) g
  have h₂ := hchar' r.val (Spec (S.residueField s)) g
  rw [hsingle] at h₁ h₂
  simpa using h₁.symm.trans h₂

/-- The complement of a member of an exhaustive increasing finite filtration all of whose
strata are compact is compact, being the union of the finitely many strata above it. -/
private lemma isCompact_compl_of_isCompact_sdiff {α : Type*} [TopologicalSpace α] {n : ℕ}
    (Z : Fin (n + 2) → Set α) (hzero : Z 0 = ∅)
    (hlast : Z (Fin.last (n + 1)) = Set.univ)
    (hmono : ∀ i : Fin (n + 1), Z i.castSucc ⊆ Z i.succ)
    (hcompact : ∀ r : Fin (n + 1), IsCompact (Z r.succ \ Z r.castSucc))
    (i : Fin (n + 2)) : IsCompact (Z i)ᶜ := by
  have hset : (Z i)ᶜ = ⋃ r : Fin (n + 1),
      if i ≤ r.castSucc then Z r.succ \ Z r.castSucc else ∅ := by
    ext s
    constructor
    · intro hs
      obtain ⟨r, hr⟩ := exists_filtration_stratum Z hzero hlast s
      have hir : i ≤ r.castSucc := by
        by_contra hn
        have hle : r.succ ≤ i := by
          have hlt : r.castSucc < i := lt_of_not_ge hn
          have hval : r.succ.val = r.castSucc.val + 1 := by simp
          apply Fin.le_iff_val_le_val.mpr
          have hltval := Fin.lt_def.mp hlt
          omega
        exact hs (filtration_subset_of_le Z hmono hle hr.1)
      simp only [Set.mem_iUnion]
      exact ⟨r, by simpa [hir] using hr⟩
    · intro hs
      simp only [Set.mem_iUnion] at hs
      obtain ⟨r, hr⟩ := hs
      split_ifs at hr with hir
      · intro hi
        exact hr.2 (filtration_subset_of_le Z hmono hir hi)
      · exact False.elim hr
  rw [hset]
  exact isCompact_iUnion fun r => by split_ifs; exacts [hcompact r, isCompact_empty]

/-- The image of the spectrum of a quotient of the global functions of an affine scheme is the zero
locus of the ideal. -/
private lemma range_quotientSpec_eq_zeroLocus
    (X : Scheme.{u}) [IsAffine X] (I : Ideal Γ(X, ⊤)) :
    Set.range
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.isoSpec.inv).base) =
      X.zeroLocus (U := ⊤) I := by
  have h : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set Γ(X, ⊤)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
  calc
    _ = X.isoSpec.inv.base '' Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
      Set.range_comp _ _
    _ = X.isoSpec.inv.base '' PrimeSpectrum.zeroLocus (I : Set Γ(X, ⊤)) :=
      congrArg (Set.image X.isoSpec.inv.base) h
    _ = X.zeroLocus (U := ⊤) I := X.isoSpec_inv_image_zeroLocus I

/-- Global sections recover a ring map from the morphism of spectra it induces. -/
private lemma specMap_appTop_comp_ΓSpecIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫
      (Scheme.ΓSpecIso S).hom = f := by
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- On the spectrum of a ring, an injection of `r` copies of an ideal into the global sections of a
quasi-coherent module is realised by a monomorphism from the coproduct of `r` copies of the
corresponding quasi-coherent ideal sheaf. -/
private lemma exists_ideal_sum_on_spec
    (R : CommRingCat.{u}) (N : (Spec R).Modules) [IsIso N.fromTildeΓ]
    (I : Ideal R) (r : ℕ)
    (φ : (Fin r → I) →ₗ[R] ((moduleSpecΓFunctor (R := R)).obj N))
    (hφ : Function.Injective φ) (g : (moduleSpecΓFunctor (R := R)).obj N)
    (hg : ∃ t, φ t = g) :
    ∃ F : (SheafOfModules.unit (Spec R).ringCatSheaf).Submodule,
      F.toSheafOfModules.IsQuasicoherent ∧
      ∃ ψ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶ N,
        Mono ψ ∧ ∃ t, Scheme.Modules.Hom.app ψ ⊤ t = g := by
  classical
  let M := ModuleCat.of R I
  let j : M ⟶ ModuleCat.of R R := ModuleCat.ofHom I.subtype
  have : Mono j := (ModuleCat.mono_iff_injective _).mpr I.injective_subtype
  obtain ⟨F, hF, ⟨eF⟩⟩ := exists_quasicoherent_ideal_of_module_mono R M j
  let e : (∐ fun _ : Fin r => M) ≅ ModuleCat.of R (Fin r → I) :=
    (biproduct.isoCoproduct (fun _ : Fin r => M)).symm ≪≫
      biproduct.isoProduct _ ≪≫ ModuleCat.piIsoPi _
  have : PreservesColimitsOfShape (Discrete (Fin r)) (tilde.functor R) :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint (tilde.functor R)
  let Ecmp := asIso (sigmaComparison (tilde.functor R) (fun _ : Fin r => M))
  let E : (∐ fun _ : Fin r => F.toSheafOfModules) ≅ tilde (ModuleCat.of R (Fin r → I)) :=
    Sigma.mapIso (fun _ => eF.symm) ≪≫ Ecmp ≪≫ (tilde.functor R).mapIso e
  let m : ModuleCat.of R (Fin r → I) ⟶ (moduleSpecΓFunctor (R := R)).obj N :=
    ModuleCat.ofHom (Y := (moduleSpecΓFunctor (R := R)).obj N) φ
  have : Mono m := (ModuleCat.mono_iff_injective _).mpr hφ
  have hmm : Mono (tilde.map m) := mono_tilde_map m
  have hmN : Mono N.fromTildeΓ := IsIso.mono_of_iso _
  have : IsIso E.hom := E.isIso_hom
  have hmE : Mono E.hom := IsIso.mono_of_iso E.hom
  let ψ := E.hom ≫ tilde.map m ≫ N.fromTildeΓ
  have hψ : Mono ψ := mono_comp' hmE (mono_comp' hmm hmN)
  obtain ⟨t, ht⟩ := hg
  refine ⟨F, hF, ψ, hψ, (Scheme.Modules.Hom.app E.inv ⊤) (tilde.toOpen _ ⊤ t), ?_⟩
  have h₁ := congrArg (fun z => z t) (tilde.toOpen_map_app m ⊤)
  have h₂ := congrArg (fun z => z (φ t)) (N.toOpen_fromTildeΓ_app ⊤)
  have hE (v : Γ(tilde (ModuleCat.of R (Fin r → I)), ⊤)) :
      Scheme.Modules.Hom.app E.hom ⊤ (Scheme.Modules.Hom.app E.inv ⊤ v) = v :=
    congrArg (fun q => Scheme.Modules.Hom.app q ⊤ v) E.inv_hom_id
  refine Eq.trans (congrArg (fun w => Scheme.Modules.Hom.app N.fromTildeΓ ⊤
    (Scheme.Modules.Hom.app (tilde.map m) ⊤ w)) (hE (tilde.toOpen _ ⊤ t))) ?_
  change Scheme.Modules.Hom.app N.fromTildeΓ ⊤
    ((modulesSpecToSheaf.map (tilde.map m)).hom.app (.op ⊤) (tilde.toOpen _ ⊤ t)) = g
  change (modulesSpecToSheaf.map (tilde.map m)).hom.app (.op ⊤) (tilde.toOpen _ ⊤ t) =
    tilde.toOpen _ ⊤ (φ t) at h₁
  rw [h₁]
  change Scheme.Modules.Hom.app N.fromTildeΓ ⊤ (tilde.toOpen _ ⊤ (φ t)) =
    ((modulesSpecToSheaf.obj N).obj.map (homOfLE (le_refl ⊤)).op) (φ t) at h₂
  have hid : ((modulesSpecToSheaf.obj N).obj.map (homOfLE (le_refl ⊤)).op) = 𝟙 _ :=
    (modulesSpecToSheaf.obj N).obj.map_id _
  rw [hid] at h₂
  exact h₂.trans ht

/-- The restriction of a global section of a module to an open subscheme. -/
private noncomputable def restrictGlobalSection {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (s : Γ(M, ⊤)) : Γ(M.restrict j, ⊤) :=
  (M.restrictAppIso j ⊤).inv (M.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op s)

/-- Restriction of global sections to an open subscheme commutes with a morphism of modules. -/
private lemma restrictGlobalSection_naturality {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor j).map φ) ⊤
      (restrictGlobalSection j M s) =
        restrictGlobalSection j N (Scheme.Modules.Hom.app φ ⊤ s) := by
  change Scheme.Modules.Hom.app φ (j ''ᵁ ⊤)
    (M.presheaf.map (homOfLE le_top).op s) =
      N.presheaf.map (homOfLE le_top).op (Scheme.Modules.Hom.app φ ⊤ s)
  exact (congrArg (fun q => q s) (Scheme.Modules.Hom.mapPresheaf φ |>.naturality
    (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op))

/-- Restriction along an open immersion preserves monomorphisms of sheaves of modules. -/
private lemma mono_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (φ : M ⟶ N) (hφ : Mono φ) :
    Mono ((Scheme.Modules.restrictFunctor j).map φ) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : @Mono (SheafOfModules Y.ringCatSheaf) _ M N φ := hφ
  have : Mono φ.val := (SheafOfModules.forget Y.ringCatSheaf).map_mono φ
  exact PresheafOfModules.injective_of_mono φ.val (.op (j ''ᵁ U.unop))

/-- A monomorphism from a sum of copies of a quasi-coherent ideal sheaf hitting a global section
restricts to one on an open subscheme. -/
private lemma exists_ideal_sum_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (N : Y.Modules) (r : ℕ) (g : Γ(N, ⊤))
    (F : (SheafOfModules.unit Y.ringCatSheaf).Submodule)
    [F.toSheafOfModules.IsQuasicoherent]
    (φ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶ N) [Mono φ]
    (t : Γ((∐ fun _ : Fin r => F.toSheafOfModules), ⊤))
    (ht : Scheme.Modules.Hom.app φ ⊤ t = g) :
    ∃ F' : (SheafOfModules.unit X.ringCatSheaf).Submodule,
      F'.toSheafOfModules.IsQuasicoherent ∧
      ∃ ψ : (∐ fun _ : Fin r => F'.toSheafOfModules) ⟶ N.restrict j,
        Mono ψ ∧ ∃ s, Scheme.Modules.Hom.app ψ ⊤ s = restrictGlobalSection j N g := by
  let G := Scheme.Modules.restrictFunctor j
  have hFι : Mono F.ι := (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (fun _ => Subtype.val_injective))
  have hGF : Mono (G.map F.ι) := mono_restrict j F.ι hFι
  have hGφ : Mono (G.map φ) := mono_restrict j φ ‹Mono φ›
  have hqc : (G.obj F.toSheafOfModules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor j F.toSheafOfModules
  have : IsIso (Scheme.Modules.restrictUnitIso j).hom :=
    (Scheme.Modules.restrictUnitIso j).isIso_hom
  let i : G.obj F.toSheafOfModules ⟶ SheafOfModules.unit X.ringCatSheaf :=
    G.map F.ι ≫ (Scheme.Modules.restrictUnitIso j).hom
  have hi : Mono i := mono_comp' hGF (IsIso.mono_of_iso _)
  obtain ⟨F', hF', ⟨e⟩⟩ :=
    @exists_quasicoherent_submodule_iso_of_mono X.Opens _ _ _ _ _
      (G.obj F.toSheafOfModules) (SheafOfModules.unit X.ringCatSheaf) hqc i hi
  let E : (∐ fun _ : Fin r => F'.toSheafOfModules) ≅
      G.obj (∐ fun _ : Fin r => F.toSheafOfModules) :=
    Sigma.mapIso (fun _ => e.symm) ≪≫
      (PreservesCoproduct.iso G (fun _ : Fin r => F.toSheafOfModules)).symm
  have : IsIso E.hom := E.isIso_hom
  let ψ := E.hom ≫ G.map φ
  have hψ : Mono ψ := mono_comp' (IsIso.mono_of_iso E.hom) hGφ
  refine ⟨F', hF', ψ, hψ,
    Scheme.Modules.Hom.app E.inv ⊤ (restrictGlobalSection j _ t), ?_⟩
  refine Eq.trans (congrArg (fun q => Scheme.Modules.Hom.app q ⊤
    (restrictGlobalSection j (∐ fun _ : Fin r => F.toSheafOfModules) t))
      (E.inv_hom_id_assoc (G.map φ))) ?_
  exact (restrictGlobalSection_naturality j φ t).trans
    (congrArg (restrictGlobalSection j N) ht)

/-- On an affine scheme, an injection of `r` copies of an ideal into the global sections of a
module whose pushforward to the spectrum is quasi-coherent is realised by a monomorphism from the
coproduct of `r` copies of a quasi-coherent ideal sheaf. -/
private lemma exists_ideal_sum_affine (Y : Scheme.{u}) [IsAffine Y] (N : Y.Modules)
    [IsIso (((Scheme.Modules.pushforward Y.isoSpec.hom).obj N).fromTildeΓ)]
    (I : Ideal Γ(Y, ⊤)) (r : ℕ)
    (φ : (Fin r → I) →ₗ[Γ(Y, ⊤)] Γ(N, ⊤)) (hφ : Function.Injective φ)
    (g : Γ(N, ⊤)) (hg : ∃ t, φ t = g) :
    ∃ F : (SheafOfModules.unit Y.ringCatSheaf).Submodule,
      F.toSheafOfModules.IsQuasicoherent ∧
      ∃ ψ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶ N,
        Mono ψ ∧ ∃ t, Scheme.Modules.Hom.app ψ ⊤ t = g := by
  let R := Γ(Y, ⊤)
  let N' := (Scheme.Modules.pushforward Y.isoSpec.hom).obj N
  let eΓ : Γ(N, ⊤) →ₗ[R] (moduleSpecΓFunctor (R := R)).obj N' := {
    toFun := id
    map_add' _ _ := rfl
    map_smul' a b := by
      change a • b = (Y.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom a)) • b
      have he : Y.isoSpec.hom.appTop = (Scheme.ΓSpecIso R).hom := Scheme.toSpecΓ_appTop Y
      rw [he]
      exact congrArg (fun c : R => c • b)
        ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.apply_symm_apply a).symm
  }
  let φ' := eΓ.comp φ
  have hφ' : Function.Injective φ' := hφ
  have hg' : ∃ t, φ' t = (show (moduleSpecΓFunctor (R := R)).obj N' from g) := hg
  obtain ⟨F, hF, ψ, hψ, t, ht⟩ := exists_ideal_sum_on_spec R N' I r φ' hφ' g hg'
  let := hF
  let := hψ
  obtain ⟨F', hF', ψ', hψ', t', ht'⟩ := exists_ideal_sum_restrict Y.isoSpec.hom N' r g F ψ t ht
  let ε := (Scheme.Modules.restrictAdjunction Y.isoSpec.hom).counit.app N
  have : IsIso ε := by dsimp [ε]; infer_instance
  refine ⟨F', hF', ψ' ≫ ε, mono_comp' hψ' (IsIso.mono_of_iso ε), t', ?_⟩
  change Scheme.Modules.Hom.app ε ⊤ (Scheme.Modules.Hom.app ψ' ⊤ t') = g
  rw [ht']
  change N.presheaf.map (eqToHom (Y.isoSpec.hom.preimage_image_eq ⊤).symm).op
    (N.presheaf.map (homOfLE le_top).op g) = g
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have he : (homOfLE (le_top : Y.isoSpec.hom ⁻¹ᵁ (Y.isoSpec.hom ''ᵁ ⊤) ≤ ⊤)).op ≫
      (eqToHom (Y.isoSpec.hom.preimage_image_eq ⊤).symm).op = 𝟙 _ := Subsingleton.elim _ _
  rw [he, CategoryTheory.Functor.map_id]
  rfl

/-- For a morphism of affine schemes, an injection of `r` copies of an ideal into the global
sections of the direct image of the structure sheaf is realised by a monomorphism from the
coproduct of `r` copies of a quasi-coherent ideal sheaf. -/
private lemma exists_ideal_sum_affine_map {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Ideal Γ(Y, ⊤)) (r : ℕ)
    (φ : (Fin r → I) →ₗ[Γ(Y, ⊤)] Γ(Stacks.Morphisms.pushforwardStructureSheaf f, ⊤))
    (hφ : Function.Injective φ) (g : Γ(Stacks.Morphisms.pushforwardStructureSheaf f, ⊤))
    (hg : ∃ t, φ t = g) :
    ∃ F : (SheafOfModules.unit Y.ringCatSheaf).Submodule,
      F.toSheafOfModules.IsQuasicoherent ∧
      ∃ ψ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶ Stacks.Morphisms.pushforwardStructureSheaf f,
        Mono ψ ∧ ∃ t, Scheme.Modules.Hom.app ψ ⊤ t = g := by
  let N := Stacks.Morphisms.pushforwardStructureSheaf f
  let N' := (Scheme.Modules.pushforward Y.isoSpec.hom).obj N
  let f' := Spec.map f.appTop
  have he : X.isoSpec.inv ≫ (f ≫ Y.isoSpec.hom) = f' := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  let e : N' ≅ Stacks.Morphisms.pushforwardStructureSheaf f' :=
    (Scheme.Modules.pushforwardComp f Y.isoSpec.hom).app (SheafOfModules.unit _) ≪≫
      Stacks.Morphisms.pushforwardStructureSheafIsoOfSourceIso X.isoSpec.symm (f ≫ Y.isoSpec.hom) ≪≫
      (Scheme.Modules.pushforwardCongr he).app (SheafOfModules.unit _)
  have : IsIso (Stacks.Morphisms.pushforwardStructureSheaf f').fromTildeΓ :=
    isIso_fromTildeΓ_pushforward (φ := f.appTop) (SheafOfModules.unit _)
  have hq : (Stacks.Morphisms.pushforwardStructureSheaf f').IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  have : N'.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso e.symm hq
  have : IsIso N'.fromTildeΓ := inferInstance
  exact exists_ideal_sum_affine Y N I r φ hφ g hg

/-- A commuting square of open immersions over `f` whose vertical arrow is a morphism of affine
schemes turns such an injection into the conclusion of Stacks 082V for the images of the two
open immersions. -/
private lemma exists_open_of_affine_injection
    {X S Y T : Scheme.{u}} [IsAffine Y] [IsAffine T]
    (f : X ⟶ S) (i : Y ⟶ X) (j : T ⟶ S) [IsOpenImmersion i] [IsOpenImmersion j]
    (p : Y ⟶ T) (hcomm : p ≫ j = i ≫ f)
    (g : Γ(X, ⊤)) (hg : i.appTop.hom g ≠ 0)
    (I : Ideal Γ(T, ⊤)) (r : ℕ) (hr : 0 < r)
    (φ : (Fin r → I) →ₗ[Γ(T, ⊤)] Γ(Stacks.Morphisms.pushforwardStructureSheaf p, ⊤))
    (hφ : Function.Injective φ) (z : Fin r → I) (hz : φ z = i.appTop.hom g) :
    ∃ (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
      (F : (SheafOfModules.unit U.toScheme.ringCatSheaf).Submodule),
      F.toSheafOfModules.IsQuasicoherent ∧
      ∃ (r : ℕ) (_hr : 0 < r)
        (ψ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶
          (Scheme.Modules.pushforward (f.resLE U V hVU)).obj (SheafOfModules.unit _)),
        Mono ψ ∧ ∃ t, Scheme.Modules.Hom.app ψ ⊤ t =
          (show Γ((Scheme.Modules.pushforward (f.resLE U V hVU)).obj
            (SheafOfModules.unit _), ⊤) from V.ι.appTop.hom g) ∧ V.ι.appTop.hom g ≠ 0 := by
  let U := j.opensRange
  let V := i.opensRange
  have hVU : V ≤ f ⁻¹ᵁ U := by
    rintro x ⟨y, rfl⟩
    exact ⟨p.base y, congrArg (fun k : Y ⟶ S => k.base y) hcomm⟩
  let p₀ := f.resLE U V hVU
  let eU : T ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq j U.ι (by simp [U])
  let eV : Y ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq i V.ι (by simp [V])
  have : IsIso eU.hom := eU.isIso_hom
  have : IsIso eV.hom := eV.isIso_hom
  have : IsIso eU.hom.appTop := inferInstanceAs (IsIso (eU.hom.app ⊤))
  have : IsIso eV.hom.appTop := inferInstanceAs (IsIso (eV.hom.app ⊤))
  have heU : eU.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have heV : eV.hom ≫ V.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hp : eV.hom ≫ p₀ = p ≫ eU.hom := by
    apply (cancel_mono U.ι).mp
    calc
      (eV.hom ≫ p₀) ≫ U.ι = eV.hom ≫ (V.ι ≫ f) := by
        rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
      _ = i ≫ f := by rw [← Category.assoc, heV]
      _ = p ≫ j := hcomm.symm
      _ = (p ≫ eU.hom) ≫ U.ι := by rw [Category.assoc, heU]
  let a : Γ(U.toScheme, ⊤) ≃+* Γ(T, ⊤) :=
    (asIso eU.hom.appTop).commRingCatIsoToRingEquiv
  let b : Γ(V.toScheme, ⊤) ≃+* Γ(Y, ⊤) :=
    (asIso eV.hom.appTop).commRingCatIsoToRingEquiv
  have haapp (x : Γ(U.toScheme, ⊤)) : a x = eU.hom.appTop.hom x := rfl
  have hbapp (x : Γ(V.toScheme, ⊤)) : b x = eV.hom.appTop.hom x := rfl
  have hab (c : Γ(U.toScheme, ⊤)) : b (p₀.appTop.hom c) = p.appTop.hom (a c) := by
    rw [hbapp, haapp]
    have h := congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ Γ(Y, ⊤) => k.hom c)
      (congrArg Scheme.Hom.appTop hp)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
  have hbg : b (V.ι.appTop.hom g) = i.appTop.hom g := by
    rw [hbapp]
    have h := congrArg (fun k : Γ(X, ⊤) ⟶ Γ(Y, ⊤) => k.hom g)
      (congrArg Scheme.Hom.appTop heV)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
  let I₀ : Ideal Γ(U.toScheme, ⊤) := I.comap a.toRingHom
  let w : (Fin r → I₀) → (Fin r → I) := fun v k => ⟨a (v k), (v k).property⟩
  let φ₀ : (Fin r → I₀) →ₗ[Γ(U.toScheme, ⊤)]
      Γ(Stacks.Morphisms.pushforwardStructureSheaf p₀, ⊤) := {
    toFun v := b.symm (φ (w v))
    map_add' v v' := by
      have hw : w (v + v') = w v + w v' := by
        ext k
        exact a.map_add (v k) (v' k)
      have h1 : φ (w (v + v')) = φ (w v) + φ (w v') := by rw [hw]; exact map_add φ _ _
      exact (congrArg (fun x : Γ(Y, ⊤) => b.symm x) h1).trans (map_add b.symm _ _)
    map_smul' c v := by
      have hw : w (c • v) = a c • w v := by
        ext k
        exact a.map_mul c (v k)
      rw [hw, map_smul]
      let m : Γ(Y, ⊤) := φ (w v)
      change b.symm (p.appTop.hom (a c) * m) =
        p₀.appTop.hom c * b.symm m
      rw [← hab, map_mul, b.symm_apply_apply]
  }
  have hφ₀ : Function.Injective φ₀ := by
    intro v v' h
    have hw : w v = w v' := hφ (b.symm.injective h)
    funext k
    exact Subtype.ext (a.injective (congrArg (fun t => (t k).val) hw))
  let z₀ : Fin r → I₀ := fun k => ⟨a.symm (z k), by
    change a (a.symm (z k)) ∈ I
    simpa only [a.apply_symm_apply] using (z k).property⟩
  have hwz : w z₀ = z := by
    ext k
    exact a.apply_symm_apply (z k)
  have hz₀ : φ₀ z₀ = V.ι.appTop.hom g := by
    change b.symm (φ (w z₀)) = _
    rw [hwz, hz, ← hbg, b.symm_apply_apply]
  have : IsAffine U.toScheme := IsAffine.of_isIso eU.inv
  have : IsAffine V.toScheme := IsAffine.of_isIso eV.inv
  obtain ⟨F, hF, ψ, hψ, t, ht⟩ := exists_ideal_sum_affine_map p₀ I₀ r φ₀ hφ₀
    (V.ι.appTop.hom g) ⟨z₀, hz₀⟩
  refine ⟨U, V, hVU, F, hF, r, hr, ψ, hψ, t, ht, ?_⟩
  intro h
  apply hg
  rw [← hbg, h, map_zero]

/-- Pulling a global section back along an open immersion keeps its germs nonzero. -/
private lemma nonzero_germ_pullback_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (g : Γ(Y, ⊤)) (x : X)
    (h : Y.presheaf.germ ⊤ (f.base x) (by trivial) g ≠ 0) :
    X.presheaf.germ ⊤ x (by trivial) (f.appTop.hom g) ≠ 0 := by
  intro hz
  apply h
  apply (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).1
  have hc := f.germ_stalkMap_apply ⊤ x (by trivial) g
  simpa only [map_zero] using hc.trans hz

/-- **Stacks 082V.** For `f : X ⟶ S` flat, locally of finite presentation and locally
quasi-finite and `g` a nonzero global function on `X`, there are opens `V ⊆ f ⁻¹ U` on which `g`
stays nonzero and a quasi-coherent ideal sheaf `F ⊆ 𝒪_U` such that a finite direct sum of `r > 0`
copies of `F` injects into `f_* 𝒪_V` with `g|_V` in the image. -/
@[stacks 082V]
public theorem exists_open_injective_ideal_sum_with_section
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    (g : Γ(X, ⊤)) (hg : g ≠ 0) :
    ∃ (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
      (F : (SheafOfModules.unit U.toScheme.ringCatSheaf).Submodule),
      F.toSheafOfModules.IsQuasicoherent ∧
      ∃ (r : ℕ) (_hr : 0 < r)
        (φ : (∐ fun _ : Fin r => F.toSheafOfModules) ⟶
          (Scheme.Modules.pushforward (f.resLE U V hVU)).obj (SheafOfModules.unit _)),
        Mono φ ∧
          ∃ t : Γ((∐ fun _ : Fin r => F.toSheafOfModules), ⊤),
            Scheme.Modules.Hom.app φ ⊤ t =
              (show Γ((Scheme.Modules.pushforward (f.resLE U V hVU)).obj
                (SheafOfModules.unit _), ⊤) from (V.ι.appTop).hom g) ∧
          (V.ι.appTop).hom g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_nonzero_germ g hg
  obtain ⟨U₀, V₀, hVU₀, hUaff, hVaff, hxV, hfxU, hgV⟩ :=
    exists_affine_restrictions f hx
  let f₀ : V₀.toScheme ⟶ U₀.toScheme := f.resLE U₀ V₀ hVU₀
  let : Flat f₀ := by dsimp [f₀]; infer_instance
  have : IsSeparated f₀ := restrictedMap_isSeparated f U₀ V₀ hVU₀ hUaff hVaff
  have hbounded : HasUniversallyBoundedFibers f₀ :=
    restrictedMap_hasBoundedFibers f U₀ V₀ hVU₀ hVaff
  obtain ⟨n, Z, hclosed, hzero, hlast, hmono, hrank⟩ :=
    AlgebraicGeometry.exists_closed_filtration_characterizing_finiteLocallyFree_rank
      f₀ hbounded
  let : IsAffine U₀.toScheme := hUaff
  let : IsAffine V₀.toScheme := hVaff
  let : CompactSpace U₀.toScheme := inferInstance
  let : QuasiSeparatedSpace U₀.toScheme := inferInstance
  have : QuasiCompact f₀ := inferInstance
  obtain ⟨Zs, Ys, ιs, -, -, -, -, -, hqcs, hranges, hchars⟩ :=
    exists_quasiCompact_stratification_of_finiteLocallyFree_rank f₀
  have hstrata : ∀ k : Fin (n + 1), IsCompact (Z k.succ \ Z k.castSucc) := by
    intro k
    rw [sdiff_eq_sdiff_of_rank_characterizations f₀ Z hrank Zs hchars k, ← hranges k.val]
    let : QuasiCompact (ιs k.val) := hqcs k.val
    let : CompactSpace (Ys k.val) :=
      (quasiCompact_iff_compactSpace (ιs k.val)).mp inferInstance
    exact isCompact_range (ιs k.val).continuous
  let g₀ : Γ(V₀.toScheme, ⊤) := (V₀.ι.appTop).hom g
  have hg₀ : g₀ ≠ 0 := restrict_appTop_ne_zero_of_germ hx V₀ hxV
  let P : V₀.toScheme → Prop := fun y =>
    V₀.toScheme.presheaf.germ ⊤ y (show y ∈ (⊤ : V₀.toScheme.Opens) from trivial) g₀ ≠ 0
  obtain ⟨y₀, hy₀⟩ := exists_nonzero_germ g₀ hg₀
  obtain ⟨r, hsupportZ, y, hy, hnotprev⟩ :=
    exists_min_filtration_level Z hzero hlast f₀.base P ⟨y₀, hy₀⟩
  have hZcompact : IsCompact (Z r.succ)ᶜ :=
    isCompact_compl_of_isCompact_sdiff Z hzero hlast hmono hstrata r.succ
  have hZretro : IsRetrocompact (Z r.succ)ᶜ :=
    hZcompact.isRetrocompact (hclosed r.succ).isOpen_compl
  let W : U₀.toScheme.Opens :=
    ⟨(Z r.castSucc)ᶜ, isOpen_compl_iff.mpr (hclosed r.castSucc)⟩
  have hfyW : f₀.base y ∈ W := hnotprev
  obtain ⟨U₁, hU₁aff, hfyU₁, hU₁W⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U₀.toScheme)
      (x := f₀.base y) (U := W) hfyW
  have hyU₁ : y ∈ f₀ ⁻¹ᵁ U₁ := by simpa using hfyU₁
  let V₁ : V₀.toScheme.Opens := f₀ ⁻¹ᵁ U₁
  have hV₁aff : IsAffineOpen V₁ := hU₁aff.preimage f₀
  have hyV₁ : y ∈ V₁ := hyU₁
  have hV₁U₁ : V₁ ≤ f₀ ⁻¹ᵁ U₁ := le_rfl
  have hgV₁ : (V₁.ι.appTop).hom g₀ ≠ 0 :=
    restrict_appTop_ne_zero_of_germ hy V₁ hyV₁
  let Z₁ : Set U₁.toScheme := U₁.ι.base ⁻¹' Z r.succ
  have hZ₁closed : IsClosed Z₁ := (hclosed r.succ).preimage U₁.ι.continuous
  have hZ₁retro : IsRetrocompact Z₁ᶜ := by
    change IsRetrocompact (U₁.ι.base ⁻¹' (Z r.succ)ᶜ)
    exact hZretro.preimage_of_isOpenEmbedding U₁.ι.isOpenEmbedding
  let : IsAffine U₁.toScheme := hU₁aff
  obtain ⟨I, hIFG, hIZ⟩ :=
    exists_fg_ideal_zeroLocus_eq_of_retrocompact_complement
      U₁.toScheme Z₁ hZ₁closed hZ₁retro
  have hIZ' : Z₁ = U₁.toScheme.zeroLocus (U := ⊤) I := hIZ.symm
  let f₁ : V₁.toScheme ⟶ U₁.toScheme := f₀.resLE U₁ V₁ hV₁U₁
  let A : Type u := Γ(U₁.toScheme, ⊤)
  let B : Type u := Γ(V₁.toScheme, ⊤)
  let : CommRing A := inferInstance
  let : CommRing B := inferInstance
  let : IsAffine V₁.toScheme := hV₁aff
  let : Flat f₁ := by
    dsimp [f₁]
    exact AlgebraicGeometry.Flat.instResLE f₀ V₁ U₁ hV₁U₁
  let : Algebra A B := f₁.appTop.hom.toAlgebra
  let : Module.Flat A B := RingHom.flat_algebraMap_iff.mp f₁.flat_appTop
  let b : B := (V₁.ι.appTop).hom g₀
  have hb : b ≠ 0 := hgV₁
  have hres (z : V₁.toScheme) : U₁.ι.base (f₁.base z) = f₀.base (V₁.ι.base z) :=
    congrArg (fun q : V₁.toScheme ⟶ U₀.toScheme => q.base z) (Scheme.Hom.resLE_comp_ι f₀ hV₁U₁)
  have hbSupport : ∀ z : V₁.toScheme,
      V₁.toScheme.presheaf.germ ⊤ z (by trivial) b ≠ 0 →
        f₁.base z ∈ U₁.toScheme.zeroLocus (U := ⊤) I := by
    intro z hz
    have hz₀ : P (V₁.ι.base z) :=
      germ_nonzero_of_open_restriction V₁ g₀ z hz
    have hzr : f₀.base (V₁.ι.base z) ∈ Z r.succ :=
      hsupportZ _ hz₀
    rw [← hres] at hzr
    rw [← hIZ']
    exact hzr
  have hpow : ∀ a ∈ I, ∃ m : ℕ, (algebraMap A B a) ^ m * b = 0 := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      exists_pow_annihilates_of_germ_support_subset f₁ b I hbSupport
  obtain ⟨J, hJFG, hJI, hJkill⟩ :=
    exists_fg_ideal_with_same_zeroLocus_annihilating b I hIFG hpow
  have hbJ := mem_annihilator_map_of_mul_eq_zero J b hJkill
  have hJzero : U₁.toScheme.zeroLocus (U := ⊤) J = Z₁ := by
    calc
      _ = U₁.toScheme.isoSpec.inv.base '' PrimeSpectrum.zeroLocus (J : Set A) :=
        (U₁.toScheme.isoSpec_inv_image_zeroLocus J).symm
      _ = U₁.toScheme.isoSpec.inv.base '' PrimeSpectrum.zeroLocus (I : Set A) := by
        rw [hJI]
      _ = U₁.toScheme.zeroLocus (U := ⊤) I :=
        U₁.toScheme.isoSpec_inv_image_zeroLocus I
      _ = Z₁ := hIZ'.symm
  let q : Spec (.of (A ⧸ J)) ⟶ U₁.toScheme :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ U₁.toScheme.isoSpec.inv
  have hq_appTop : q.appTop ≫ (Scheme.ΓSpecIso (.of (A ⧸ J))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    have htop : U₁.toScheme.isoSpec.inv.appTop =
        (Scheme.ΓSpecIso (.of A)).inv := by
      have hhom : U₁.toScheme.isoSpec.hom.appTop =
          (Scheme.ΓSpecIso (.of A)).hom := Scheme.toSpecΓ_appTop _
      apply (cancel_mono (Scheme.ΓSpecIso (.of A)).hom).mp
      rw [Iso.inv_hom_id]
      rw [← hhom]
      simp only [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    change (U₁.toScheme.isoSpec.inv.appTop ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop) ≫
        (Scheme.ΓSpecIso (.of (A ⧸ J))).hom = _
    rw [htop]
    exact specMap_appTop_comp_ΓSpecIso (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hqrange : Set.range q.base = Z₁ :=
    (range_quotientSpec_eq_zeroLocus U₁.toScheme J).trans hJzero
  let q₀ : Spec (.of (A ⧸ J)) ⟶ U₀.toScheme := q ≫ U₁.ι
  have hqstratum : Set.range q₀.base ⊆ Z r.succ \ Z r.castSucc := by
    rintro s ⟨t, rfl⟩
    have ht : q.base t ∈ Z₁ := hqrange ▸ Set.mem_range_self t
    have ht' : U₁.ι.base (q.base t) ∈ Z r.succ := ht
    have hw : U₁.ι.base (q.base t) ∈ W := hU₁W (q.base t).2
    exact ⟨ht', hw⟩
  have hqrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f₀ q₀) r.val :=
    (hrank r _ q₀).2 hqstratum
  have hqrank₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f₁ q) r.val := by
    have hf₁ : f₁ = f₀ ∣_ U₁ := f₀.resLE_eq_morphismRestrict
    rw [hf₁]
    exact (rank_pullback_symmetry (f₀ ∣_ U₁) q r.val).mp
      ((finiteLocallyFreeOfRank_baseChange_open_iff f₀ U₁ q r.val).mpr
        ((rank_pullback_symmetry f₀ q₀ r.val).mpr hqrank))
  let Mq : (Spec (.of (A ⧸ J))).Modules :=
    Stacks.Morphisms.pushforwardStructureSheaf (pullback.snd f₁ q)
  have hqmodule : Module.IsFiniteLocallyFreeOfRank (A ⧸ J)
      ((modulesSpecToSheaf.obj Mq).presheaf.obj (.op ⊤)) r.val := by
    let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Mq r.val :=
      hqrank₁.toIsFiniteLocallyFreeOfRank
    exact module_isFiniteLocallyFreeOfRank_of_sheafRank_spec (.of (A ⧸ J)) Mq r.val
  let C : Type u := Γ(pullback f₁ q, ⊤)
  let : CommRing C := inferInstance
  let : Algebra (A ⧸ J) C :=
    (((Scheme.ΓSpecIso (.of (A ⧸ J))).inv ≫
      (pullback.snd f₁ q).appTop).hom).toAlgebra
  have hCrank : Module.IsFiniteLocallyFreeOfRank (A ⧸ J) C r.val := by
    change Module.IsFiniteLocallyFreeOfRank (A ⧸ J)
      ((modulesSpecToSheaf.obj Mq).presheaf.obj (.op ⊤)) r.val
    exact hqmodule
  let Rq : Type u := Γ(Spec (.of (A ⧸ J)), ⊤)
  let : CommRing Rq := inferInstance
  let : Algebra A Rq := q.appTop.hom.toAlgebra
  let eRq : Rq ≃ₐ[A] A ⧸ J := {
    toRingEquiv := (Scheme.ΓSpecIso (.of (A ⧸ J))).commRingCatIsoToRingEquiv
    commutes' a := by
      have h := congrArg
        (fun k : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J) => k.hom a) hq_appTop
      exact h
  }
  have hpush : IsPushout f₁.appTop q.appTop
      (pullback.fst f₁ q).appTop (pullback.snd f₁ q).appTop :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f₁ q)
  let eC : (B ⊗[A] Rq) ≃+* C :=
    ((CommRingCat.isPushout_tensorProduct A B Rq).isoPushout ≪≫
      hpush.isoPushout.symm).commRingCatIsoToRingEquiv
  let : Algebra Rq (B ⊗[A] Rq) :=
    Algebra.TensorProduct.includeRight.toRingHom.toAlgebra
  have heC_right (a : Rq) :
      eC (algebraMap Rq (B ⊗[A] Rq) a) =
        (pullback.snd f₁ q).appTop.hom a := by
    let T := CommRingCat.isPushout_tensorProduct A B Rq
    have hcat : (CommRingCat.ofHom (algebraMap Rq (B ⊗[A] Rq))) ≫
        (T.isoPushout ≪≫ hpush.isoPushout.symm).hom =
          (pullback.snd f₁ q).appTop := by
      calc
        _ = pushout.inr f₁.appTop q.appTop ≫ hpush.isoPushout.inv := by
          change (CommRingCat.ofHom (algebraMap Rq (B ⊗[A] Rq))) ≫
            (T.isoPushout.hom ≫ hpush.isoPushout.inv) = _
          exact congrArg (· ≫ hpush.isoPushout.inv) T.inr_isoPushout_hom
        _ = (pullback.snd f₁ q).appTop := hpush.inr_isoPushout_inv
    exact congrArg (fun k : CommRingCat.of Rq ⟶ CommRingCat.of C => k.hom a) hcat
  let eBC : (B ⧸ Ideal.map (algebraMap A B) J) ≃+* C :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) eRq).symm.toRingEquiv.trans eC)
  let : Algebra (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J) := inferInstance
  let eBCAlg : (B ⧸ Ideal.map (algebraMap A B) J) ≃ₐ[A ⧸ J] C := {
    toRingEquiv := eBC
    commutes' x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hmk : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J)
          ((algebraMap (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
            (Ideal.Quotient.mk J a)) =
            (1 : B) ⊗ₜ[A] (Ideal.Quotient.mk J a) := by
        rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
          Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul a
      have hcongr :
          (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) eRq).symm
            ((1 : B) ⊗ₜ[A] (Ideal.Quotient.mk J a)) =
              (1 : B) ⊗ₜ[A] (eRq.symm (Ideal.Quotient.mk J a)) := by
        rw [Algebra.TensorProduct.congr_symm_apply,
          Algebra.TensorProduct.map_tmul]
        simp
      have heRq : eRq.symm (Ideal.Quotient.mk J a) =
          (Scheme.ΓSpecIso (.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a) := rfl
      change eBC ((algebraMap (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
          (Ideal.Quotient.mk J a)) =
        (algebraMap (A ⧸ J) C) (Ideal.Quotient.mk J a)
      rw [show eBC _ = eC
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) eRq).symm
          ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J)
            ((algebraMap (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
              (Ideal.Quotient.mk J a)))) from rfl]
      rw [hmk, hcongr, heRq]
      change eC ((1 : B) ⊗ₜ[A]
          (Scheme.ΓSpecIso (.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a)) =
        (pullback.snd f₁ q).appTop.hom
          ((Scheme.ΓSpecIso (.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a))
      simpa only [Algebra.TensorProduct.right_algebraMap_apply] using
        heC_right ((Scheme.ΓSpecIso (.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a))
  }
  have hQuotRank : Module.IsFiniteLocallyFreeOfRank (A ⧸ J)
      (B ⧸ Ideal.map (algebraMap A B) J) r.val :=
    locallyFreeRank_of_linearEquiv eBCAlg.symm.toLinearEquiv hCrank
  let y₁ : V₁.toScheme := ⟨y, hyV₁⟩
  have hyZ₁ : f₁.base y₁ ∈ Z₁ := by
    change U₁.ι.base (f₁.base y₁) ∈ Z r.succ
    rw [hres]
    exact hsupportZ y hy
  obtain ⟨t, ht⟩ : f₁.base y₁ ∈ Set.range q.base := hqrange.symm ▸ hyZ₁
  obtain ⟨ι, s, hspan, hbasis⟩ := hQuotRank
  have htcover : t ∈ (⨆ i : ι, PrimeSpectrum.basicOpen (s i)) := by
    rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hspan]
    trivial
  have htcover' : t ∈
      ⋃ i : ι, (PrimeSpectrum.basicOpen (s i) : Set (PrimeSpectrum (A ⧸ J))) :=
    Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp htcover)
  obtain ⟨i, hti⟩ := Set.mem_iUnion.mp htcover'
  obtain ⟨basis⟩ := hbasis i
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s i)
  let U₂ := U₁.toScheme.basicOpen a
  let V₂ := V₁.toScheme.basicOpen (f₁.appTop.hom a)
  have hV₂ : V₂ = f₁ ⁻¹ᵁ U₂ := (Scheme.preimage_basicOpen f₁ a).symm
  have hVU₂ : V₂ ≤ f₁ ⁻¹ᵁ U₂ := hV₂.le
  have hyU₂ : f₁.base y₁ ∈ U₂ := by
    rw [← ht]
    change t ∈ q ⁻¹ᵁ U₂
    rw [show q ⁻¹ᵁ U₂ = (Spec (.of (A ⧸ J))).basicOpen (q.appTop.hom a) from
      Scheme.preimage_basicOpen q a]
    rw [basicOpen_eq_of_affine']
    have hqa := congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J) => k.hom a)
      hq_appTop
    change t ∈ PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso (.of (A ⧸ J))).hom.hom
      (q.appTop.hom a))
    change (Scheme.ΓSpecIso (.of (A ⧸ J))).hom.hom (q.appTop.hom a) =
      Ideal.Quotient.mk J a at hqa
    rw [hqa, ha]
    exact hti
  have hyV₂ : y₁ ∈ V₂ := hV₂ ▸ hyU₂
  let f₂ := f₁.resLE U₂ V₂ hVU₂
  let A₂ := Γ(U₂.toScheme, ⊤)
  let B₂ := Γ(V₂.toScheme, ⊤)
  let : Algebra A₂ B₂ := f₂.appTop.hom.toAlgebra
  let : Algebra A B₂ := ((V₂.ι.appTop).hom.comp f₁.appTop.hom).toAlgebra
  have : IsScalarTower A B B₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A A₂ B₂ := by
    apply IsScalarTower.of_algebraMap_eq'
    have h := congrArg Scheme.Hom.appTop (Scheme.Hom.resLE_comp_ι f₁ hVU₂)
    exact congrArg CommRingCat.Hom.hom h.symm
  have : IsAffine U₂.toScheme := (isAffineOpen_top U₁.toScheme).basicOpen a
  have : IsAffine V₂.toScheme := (isAffineOpen_top V₁.toScheme).basicOpen (f₁.appTop.hom a)
  have : Flat f₂ := by dsimp [f₂]; infer_instance
  have : Module.Flat A₂ B₂ := RingHom.flat_algebraMap_iff.mp f₂.flat_appTop
  let K : Ideal A₂ := J.map (algebraMap A A₂)
  have hK : K.FG := hJFG.map _
  let b₂ : B₂ := V₂.ι.appTop.hom b
  have hb₂ : b₂ ≠ 0 :=
    restrict_appTop_ne_zero_of_germ (nonzero_germ_pullback_open V₁.ι g₀ y₁ hy) V₂ hyV₂
  have hb₂K : b₂ ∈ Submodule.annihilator (K.map (algebraMap A₂ B₂)) := by
    rw [show K.map (algebraMap A₂ B₂) = J.map (algebraMap A B₂) by
      simp only [K, Ideal.map_map]
      exact congrArg (fun h => J.map h) (IsScalarTower.algebraMap_eq A A₂ B₂).symm]
    refine mem_annihilator_map_of_mul_eq_zero J b₂ fun z hz => ?_
    change V₂.ι.appTop.hom (algebraMap A B z) * V₂.ι.appTop.hom b = 0
    rw [← map_mul, hJkill z hz, map_zero]
  have hbasis' : Module.Basis (Fin r.val) (Localization.Away (Ideal.Quotient.mk J a))
      (LocalizedModule (.powers (Ideal.Quotient.mk J a))
        (B ⧸ Ideal.map (algebraMap A B) J)) := ha ▸ basis
  let e₂ := quotientLocalBasis (A' := A₂) (B' := B₂) a J hbasis'
  obtain ⟨hr, φ, hφ, z, hz⟩ :=
    exists_injective_annihilator_fin_with_preimage_positive K hK r.val e₂ b₂ hb₂K hb₂
  let i₂ : V₂.toScheme ⟶ X := V₂.ι ≫ V₁.ι ≫ V₀.ι
  let j₂ : U₂.toScheme ⟶ S := U₂.ι ≫ U₁.ι ≫ U₀.ι
  have hsq : f₂ ≫ j₂ = i₂ ≫ f := by
    dsimp only [i₂, j₂]
    rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.Hom.resLE_comp_ι]
    simp only [Category.assoc]
  have hgb : i₂.appTop.hom g = b₂ := rfl
  exact exists_open_of_affine_injection f i₂ j₂ f₂ hsq g
    (by rw [hgb]; exact hb₂) (Submodule.annihilator K) r.val hr φ hφ z (hz.trans hgb.symm)

end AlgebraicGeometry

end
