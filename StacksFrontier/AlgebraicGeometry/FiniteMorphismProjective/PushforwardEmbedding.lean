module

public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Separated
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.AffineChartSections
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# The closed immersion of a finite scheme into the projective bundle of `f_*𝒪_X`

Let `f : X ⟶ S` be an affine morphism and `ℰ = f_*𝒪_X`. This file constructs the morphism

`σ : X ⟶ 𝐏(ℰ) = Proj_S(Sym(ℰ))`

over `S` of the proof of [Stacks, Tag 0B3I], and proves it is an immersion, hence a closed
immersion when `f` is finite.

Over an affine open `V` of the base write `R = Γ(S, V)` and `A = Γ(X, f⁻¹(V)) = Γ(V, ℰ)`. The
graded ring of sections of `Sym(ℰ)` over `V` is `Sym_R(A)`
(`Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen`), and multiplication in `A` is a
ring homomorphism `Sym_R(A) → A` sending the degree-one element `1 ∈ A` to `1`. It therefore
induces a surjection `Sym_R(A)_{(1)} → A` from the degree-zero homogeneous localization at that
element, whose spectrum is a closed immersion `Spec A ⟶ D₊(1) ⊆ Proj Sym_R(A)`. These are the
morphisms `X → 𝐏ⁿ_S`, `X → D₊(T₀)` of the source's proof, read in `𝐏(ℰ)` directly. They are
compatible with restriction between affine opens of the base, because the multiplication maps and
the element `1` are; so they glue along the directed cover of `X` by the inverse images of the
affine opens of `S`.

## Main definitions

* `Stacks.FiniteMorphismProjective.structurePushforward`: the module `f_*𝒪_X`.
* `Stacks.FiniteMorphismProjective.sectionLift`: the multiplication map
  `Γ(V, Sym(f_*𝒪_X)) → Γ(X, f⁻¹(V))` over an affine open `V`.
* `Stacks.FiniteMorphismProjective.chartEmbedding`: the local morphism
  `Spec Γ(X, f⁻¹(V)) ⟶ Proj Γ(V, Sym(f_*𝒪_X))`.
* `Stacks.FiniteMorphismProjective.embedding`: the glued morphism `X ⟶ 𝐏(f_*𝒪_X)`.

## Main results

* `Stacks.FiniteMorphismProjective.embedding_comp_toBase`: the embedding is over `S`.
* `Stacks.FiniteMorphismProjective.isPullback_chart`: over the chart of an affine open `V` of the
  base, the embedding is the chart morphism on `f⁻¹(V)`.
* `Stacks.FiniteMorphismProjective.isImmersion_embedding`: the embedding is an immersion.
* `Stacks.FiniteMorphismProjective.isClosedImmersion_embedding`: for `f` finite it is a closed
  immersion.

## Implementation notes

The source obtains `σ` from the universal property of the projective bundle (Constructions, Lemma
27.16.11) applied to the surjection `f^*f_*𝒪_X → 𝒪_X`. Here `σ` is built by hand from its
restrictions over the affine opens of the base instead: `Proj_S` is constructed as a colimit of
its affine charts, which describes morphisms out of it, and the local description of `σ` is the
one the source's proof verifies anyway. The surjection used in each chart is the one of
`Stacks.FiniteMorphismProjective.awayEvalOfEqOne_surjective`, the evaluation of a homogeneous
fraction `a / 1ⁿ` at `a`; it is surjective already from degree one.

## References

* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OD](https://stacks.math.columbia.edu/tag/01OD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.FiniteMorphismProjective

universe u

/-! ### Evaluation of a degree-zero homogeneous fraction at a degree-one element sent to `1` -/

section AwayEval

open HomogeneousLocalization

variable {A T : Type u} [CommRing A] [CommRing T] {σ : Type u} [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (μ : A →+* T) {s : A} (hμ : μ s = 1)

/-- For a ring homomorphism `μ` sending `s` to `1`, the homomorphism `A_{(s)} → T` sending a
homogeneous fraction `a / s ^ n` to `μ a`. -/
def awayEvalOfEqOne : Away 𝒜 s →+* T :=
  (Localization.awayLift μ s (isUnit_iff_exists_inv.mpr ⟨1, by rw [hμ, one_mul]⟩)).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

theorem awayEvalOfEqOne_mk {d : ℕ} (hs : s ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayEvalOfEqOne 𝒜 μ hμ (Away.mk 𝒜 hs n a ha) = μ a := by
  rw [awayEvalOfEqOne, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.awayLift_mk μ s a 1 (by rw [hμ, one_mul]), one_pow, mul_one]

theorem awayEvalOfEqOne_fromZeroRingHom (a : 𝒜 0) :
    awayEvalOfEqOne 𝒜 μ hμ (fromZeroRingHom 𝒜 _ a) = μ a := by
  rw [awayEvalOfEqOne, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change Localization.awayLift μ s _ (Localization.mk (a : A) 1) = μ a
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.lift_eq _ _

/-- `awayEvalOfEqOne` is surjective as soon as every element of `T` is the image of a homogeneous
element of the degree of `s`. -/
theorem awayEvalOfEqOne_surjective {d : ℕ} (hs : s ∈ 𝒜 d)
    (hsurj : ∀ y : T, ∃ a ∈ 𝒜 d, μ a = y) : Function.Surjective (awayEvalOfEqOne 𝒜 μ hμ) := by
  intro y
  obtain ⟨a, ha, rfl⟩ := hsurj y
  exact ⟨Away.mk 𝒜 hs 1 a (by rwa [one_smul]), awayEvalOfEqOne_mk 𝒜 μ hμ hs 1 a _⟩

/-- **Compatibility of `awayEvalOfEqOne` with a graded homomorphism.** For `ψ : 𝒜 →+*ᵍ ℬ`
carrying `s` to `s'`, evaluations `μ` and `μ'` sending `s` and `s'` to `1`, and `ρ : T →+* T'` with
`ρ ∘ μ = μ' ∘ ψ`, the two composites `Spec T' ⟶ Proj 𝒜` through the standard charts agree. -/
theorem specMap_awayEvalOfEqOne_awayι_comp_map {B T' : Type u} [CommRing B] [CommRing T']
    {τ : Type u} [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hs : s ∈ 𝒜 1) {s' : B} (hs' : s' ∈ ℬ 1) (hss' : ψ s = s') (μ' : B →+* T')
    (hμ' : μ' s' = 1) (ρ : T →+* T') (hρ : ∀ a, ρ (μ a) = μ' (ψ a)) :
    Spec.map (CommRingCat.ofHom (awayEvalOfEqOne ℬ μ' hμ')) ≫ Proj.awayι ℬ s' hs' Nat.one_pos ≫
        Proj.map ψ hψ =
      Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (awayEvalOfEqOne 𝒜 μ hμ)) ≫
        Proj.awayι 𝒜 s hs Nat.one_pos := by
  subst hss'
  rw [Proj.awayι_comp_map ψ hψ Nat.one_pos s hs, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  simp only [RingHom.comp_apply, Away.map_mk, awayEvalOfEqOne_mk, hρ]

end AwayEval

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The module `f_*𝒪_X` on the base. -/
abbrev structurePushforward : S.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- The sections of `f_*𝒪_X` over `U`, which are the functions on `f⁻¹(U)`, as a linear map
into the ring of those functions with its `Γ(S, U)`-algebra structure through `f`. -/
def sectionsToRing (U : S.Opens) :
    letI := (f.app U).hom.toAlgebra
    Γ(structurePushforward f, U) →ₗ[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) :=
  letI := (f.app U).hom.toAlgebra
  { toFun := fun m => m
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The multiplication `Sym_{Γ(S, U)}(Γ(f_*𝒪_X, U)) → Γ(X, f⁻¹(U))`. -/
def symLift (U : S.Opens) :
    SymmetricAlgebra Γ(S, U) Γ(structurePushforward f, U) →+* Γ(X, f ⁻¹ᵁ U) :=
  letI := (f.app U).hom.toAlgebra
  (SymmetricAlgebra.lift (sectionsToRing f U)).toRingHom

theorem symLift_ι (U : S.Opens) (m : Γ(structurePushforward f, U)) :
    symLift f U (SymmetricAlgebra.ι _ _ m) = (m : Γ(X, f ⁻¹ᵁ U)) := by
  let := (f.app U).hom.toAlgebra
  exact SymmetricAlgebra.lift_ι_apply (sectionsToRing f U) m

theorem symLift_algebraMap (U : S.Opens) (r : Γ(S, U)) :
    symLift f U (algebraMap _ _ r) = f.app U r := by
  let := (f.app U).hom.toAlgebra
  exact (SymmetricAlgebra.lift (sectionsToRing f U)).commutes r

/-! ### The multiplication on the sections of `Sym(f_*𝒪_X)` over an affine open -/

variable [IsAffineHom f]

/-- **`f_*𝒪_X` is quasi-coherent for an affine morphism.** -/
instance isQuasicoherent_structurePushforward : (structurePushforward f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _

/-- The sheafification unit `Sym^n_{Γ(S, V)}(Γ(f_*𝒪_X, V)) ⟶ Γ(V, Sym^n(f_*𝒪_X))` over an affine
open `V`, as an additive equivalence. -/
def symPieceAddEquiv {V : S.Opens} (hV : IsAffineOpen V) (n : ℤ) :
    (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val n).obj (op V) ≃+
      ((Scheme.Modules.symmetricAlgebra S (structurePushforward f)).piece n).val.obj (op V) :=
  AddEquiv.ofBijective
    ((PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf) (𝟙 S.ringCatSheaf.obj)
      (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val n)).app
        (op V)).hom.toAddMonoidHom
    (Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen _ hV n)

/-- A sectionwise homogeneous element of the symmetric algebra, as an element of the symmetric
algebra of the sections. -/
def pieceVal (V : S.Opens) (n : ℤ) :
    (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val n).obj (op V) →+
      SymmetricAlgebra Γ(S, V) Γ(structurePushforward f, V) where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The degree-`n` part of the multiplication map
`Γ(V, Sym(f_*𝒪_X)) → Γ(X, f⁻¹(V))` over an affine open `V`. -/
def pieceLift {V : S.Opens} (hV : IsAffineOpen V) (n : ℕ) :
    (Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra
      (structurePushforward f)).sectionPieces V n →+ Γ(X, f ⁻¹ᵁ V) :=
  (symLift f V).toAddMonoidHom.comp
    ((pieceVal f V (n : ℤ)).comp (symPieceAddEquiv f hV (n : ℤ)).symm.toAddMonoidHom)

theorem pieceLift_unit {V : S.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (x : (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val (n : ℤ)).obj (op V)) :
    pieceLift f hV n (symPieceAddEquiv f hV (n : ℤ) x) = symLift f V x.val := by
  change symLift f V (pieceVal f V (n : ℤ)
    ((symPieceAddEquiv f hV (n : ℤ)).symm (symPieceAddEquiv f hV (n : ℤ) x))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem symPieceAddEquiv_apply {V : S.Opens} (hV : IsAffineOpen V) (n : ℤ)
    (x : (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val n).obj (op V)) :
    symPieceAddEquiv f hV n x =
      (PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf) (𝟙 S.ringCatSheaf.obj)
        (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val n)).app (op V) x := rfl

theorem pieceLift_one {V : S.Opens} (hV : IsAffineOpen V) :
    pieceLift f hV 0
      ((Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra (structurePushforward f)).one V)
      = 1 := by
  have h := pieceLift_unit f hV 0
    ((Stacks.SymGraded.sitePresheafAlgebra (structurePushforward f).val).one.eval (op V))
  exact h.trans (map_one (symLift f V))

theorem pieceLift_mul {V : S.Opens} (hV : IsAffineOpen V) {i j : ℕ}
    (a : (Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra
      (structurePushforward f)).sectionPieces V i)
    (b : (Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra
      (structurePushforward f)).sectionPieces V j) :
    pieceLift f hV (i + j) (GradedMonoid.GMul.mul a b) =
      pieceLift f hV i a * pieceLift f hV j b := by
  obtain ⟨x, rfl⟩ := (symPieceAddEquiv f hV (i : ℤ)).surjective a
  obtain ⟨y, rfl⟩ := (symPieceAddEquiv f hV (j : ℤ)).surjective b
  rw [pieceLift_unit, pieceLift_unit]
  have h := pieceLift_unit f hV (i + j)
    ((Stacks.SymGraded.siteMul (structurePushforward f).val (i : ℤ) (j : ℤ)).app (op V) x y)
  have hm := Stacks.SymGraded.symmetricAlgebra_mul_unit (structurePushforward f) (i : ℤ) (j : ℤ)
    (op V) x y
  exact ((congrArg (pieceLift f hV (i + j)) hm).trans h).trans
    (map_mul (symLift f V) x.val y.val)

local notation "𝒮" => Stacks.AlgebraicGeometry.ProjBundleSurjection.symAlgebra
  (structurePushforward f)

/-- **The multiplication map `Γ(V, Sym(f_*𝒪_X)) → Γ(X, f⁻¹(V))`** over an affine open `V` of the
base, as a ring homomorphism out of the graded ring of sections. -/
def sectionLift {V : S.Opens} (hV : IsAffineOpen V) : (𝒮).sectionRing V →+* Γ(X, f ⁻¹ᵁ V) :=
  DirectSum.toSemiring (pieceLift f hV) (pieceLift_one f hV) (fun a b => pieceLift_mul f hV a b)

theorem sectionLift_of {V : S.Opens} (hV : IsAffineOpen V) {n : ℕ} (a : (𝒮).sectionPieces V n) :
    sectionLift f hV (DirectSum.of _ n a) = pieceLift f hV n a :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The sheafification unit on the degree-one generators: the section of `Sym¹(f_*𝒪_X)` over `V`
given by a section of `f_*𝒪_X`. -/
def degreeOneSection (V : S.Opens) (m : Γ(structurePushforward f, V)) : (𝒮).sectionPieces V 1 :=
  (PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf) (𝟙 S.ringCatSheaf.obj)
    (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val 1)).app (op V)
    (Stacks.SymGraded.ιG (R := Γ(S, V)) Γ(structurePushforward f, V) m)

theorem pieceLift_degreeOneSection {V : S.Opens} (hV : IsAffineOpen V)
    (m : Γ(structurePushforward f, V)) :
    pieceLift f hV 1 (degreeOneSection f V m) = (m : Γ(X, f ⁻¹ᵁ V)) :=
  (pieceLift_unit f hV 1 _).trans (symLift_ι f V m)

/-- The unit function `1 ∈ Γ(X, f⁻¹(V))`, as a section of `f_*𝒪_X` over `V`. -/
def unitSection (V : S.Opens) : Γ(structurePushforward f, V) := (1 : Γ(X, f ⁻¹ᵁ V))

/-- The unit function `1 ∈ Γ(X, f⁻¹(V))`, as a section of `Sym¹(f_*𝒪_X)` over `V`, placed in the
graded ring of sections. This is the element `T₀ ↦ 1` of the proof of Tag 0B3I. -/
def oneSection (V : S.Opens) : (𝒮).sectionRing V :=
  DirectSum.of _ 1 (degreeOneSection f V (unitSection f V))

theorem oneSection_mem (V : S.Opens) : oneSection f V ∈ (𝒮).grading V 1 :=
  (𝒮).of_mem_grading V _

theorem sectionLift_oneSection {V : S.Opens} (hV : IsAffineOpen V) :
    sectionLift f hV (oneSection f V) = 1 :=
  (sectionLift_of f hV _).trans (pieceLift_degreeOneSection f hV _)

theorem exists_sectionLift_eq {V : S.Opens} (hV : IsAffineOpen V) (y : Γ(X, f ⁻¹ᵁ V)) :
    ∃ a ∈ (𝒮).grading V 1, sectionLift f hV a = y :=
  ⟨DirectSum.of _ 1 (degreeOneSection f V y), (𝒮).of_mem_grading V _,
    (sectionLift_of f hV _).trans (pieceLift_degreeOneSection f hV _)⟩

/-! ### Compatibility with restriction -/

/-- Restriction of sections of `f_*𝒪_X`, as a semilinear map over restriction of functions on the
base. -/
def restrictₛₗ {U V : S.Opens} (h : U ≤ V) :
    Γ(structurePushforward f, V) →ₛₗ[(S.presheaf.map (homOfLE h).op).hom]
      Γ(structurePushforward f, U) where
  toFun m := (structurePushforward f).presheaf.map (homOfLE h).op m
  map_add' := map_add _
  map_smul' r m := (structurePushforward f).map_smul (homOfLE h) r m

omit [IsAffineHom f] in
/-- **The multiplication maps commute with restriction.** -/
theorem symLift_mapₛₗ {U V : S.Opens} (h : U ≤ V)
    (y : SymmetricAlgebra Γ(S, V) Γ(structurePushforward f, V)) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op (symLift f V y) =
      symLift f U (SymmetricAlgebra.mapₛₗ (S.presheaf.map (homOfLE h).op).hom
        (restrictₛₗ f h) y) := by
  have key := SymmetricAlgebra.ringHom_ext
    (f := (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.comp (symLift f V))
    (g := (symLift f U).comp (SymmetricAlgebra.mapₛₗ (S.presheaf.map (homOfLE h).op).hom
        (restrictₛₗ f h))) (fun r => ?_) (fun m => ?_)
  · exact congrArg (fun g => g y) key
  · simp only [RingHom.comp_apply, symLift_algebraMap, SymmetricAlgebra.mapₛₗ_algebraMap]
    exact (congrArg (fun g => g r) (congrArg CommRingCat.Hom.hom
      (f.naturality (homOfLE h).op))).symm
  · simp only [RingHom.comp_apply, symLift_ι, SymmetricAlgebra.mapₛₗ_ι]
    rfl

/-- Restriction of sections of `Sym^n(f_*𝒪_X)` is compatible with the sheafification unit. -/
private theorem resPiece_sheafifyUnit_app {U V : S.Opens} (h : U ≤ V) (n : ℕ)
    (x : (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val (n : ℤ)).obj (op V)) :
    (𝒮).resPiece h n ((PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf)
      (𝟙 S.ringCatSheaf.obj)
        (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val (n : ℤ))).app (op V) x) =
      (PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf) (𝟙 S.ringCatSheaf.obj)
        (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val (n : ℤ))).app (op U)
        ((Stacks.SymGraded.siteGradedPiece (structurePushforward f).val (n : ℤ)).map
          (homOfLE h).op x) :=
  (PresheafOfModules.naturality_apply (PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf)
    (𝟙 S.ringCatSheaf.obj) (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val
      (n : ℤ))) (homOfLE h).op x).symm

theorem pieceLift_resPiece {U V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) (n : ℕ) (a : (𝒮).sectionPieces V n) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op (pieceLift f hV n a) =
      pieceLift f hU n ((𝒮).resPiece h n a) := by
  obtain ⟨x, rfl⟩ := (symPieceAddEquiv f hV (n : ℤ)).surjective a
  rw [pieceLift_unit]
  refine Eq.trans ?_ ((congrArg (pieceLift f hU n) (resPiece_sheafifyUnit_app f h n x)).trans
    (pieceLift_unit f hU n _)).symm
  exact symLift_mapₛₗ f h x.val

theorem sectionLift_res {U V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) (a : (𝒮).sectionRing V) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op (sectionLift f hV a) =
      sectionLift f hU ((𝒮).res h a) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n y =>
    change _ = sectionLift f hU ((𝒮).resRingHom h _)
    rw [(𝒮).resRingHom_of, sectionLift_of, sectionLift_of]
    exact pieceLift_resPiece f hU hV h n y
  | add x y hx hy => simp only [map_add, hx, hy]

theorem resPiece_degreeOneSection {U V : S.Opens} (h : U ≤ V) (m : Γ(structurePushforward f, V)) :
    (𝒮).resPiece h 1 (degreeOneSection f V m) = degreeOneSection f U (restrictₛₗ f h m) := by
  refine (resPiece_sheafifyUnit_app f h 1 _).trans ?_
  unfold degreeOneSection
  congr 1
  exact Subtype.ext (SymmetricAlgebra.mapₛₗ_ι (S.presheaf.map (homOfLE h).op).hom
    (restrictₛₗ f h) m)

theorem res_oneSection {U V : S.Opens} (h : U ≤ V) :
    (𝒮).res h (oneSection f V) = oneSection f U := by
  change (𝒮).resRingHom h _ = _
  rw [oneSection, (𝒮).resRingHom_of, resPiece_degreeOneSection]
  have h1 : restrictₛₗ f h (unitSection f V) = unitSection f U :=
    map_one (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom
  rw [h1]
  rfl

/-! ### The chart morphisms -/

/-- **The local form of the embedding.** Over an affine open `V` of the base,
`Spec Γ(X, f⁻¹(V)) ⟶ Proj Γ(V, Sym(f_*𝒪_X))`: the closed immersion into the standard chart
`D₊(1)` cut out by the surjection `Γ(V, Sym(f_*𝒪_X))_{(1)} → Γ(X, f⁻¹(V))`, followed by the open
immersion of that chart. -/
def chartEmbedding {V : S.Opens} (hV : IsAffineOpen V) :
    Spec Γ(X, f ⁻¹ᵁ V) ⟶ Proj ((𝒮).grading V) :=
  Spec.map (CommRingCat.ofHom
      (awayEvalOfEqOne ((𝒮).grading V) (sectionLift f hV) (sectionLift_oneSection f hV))) ≫
    Proj.awayι ((𝒮).grading V) (oneSection f V) (oneSection_mem f V) Nat.one_pos

theorem isImmersion_chartEmbedding {V : S.Opens} (hV : IsAffineOpen V) :
    IsImmersion (chartEmbedding f hV) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (awayEvalOfEqOne ((𝒮).grading V) (sectionLift f hV) (sectionLift_oneSection f hV)))) :=
    IsClosedImmersion.spec_of_surjective _
      (awayEvalOfEqOne_surjective ((𝒮).grading V) (sectionLift f hV) (sectionLift_oneSection f hV)
        (oneSection_mem f V) (exists_sectionLift_eq f hV))
  exact inferInstanceAs (IsImmersion (_ ≫ _))

/-- **The chart morphisms are compatible with restriction.** -/
@[reassoc]
theorem chartEmbedding_comp_projInclusionMap {U V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ≤ V) :
    chartEmbedding f hU ≫ projInclusionMap (𝒮) U V h hU hV =
      Spec.map (X.presheaf.map (homOfLE (f.preimage_mono h)).op) ≫ chartEmbedding f hV := by
  have hirr := Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
        (𝒮).toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h
  have hmap : projInclusionMap (𝒮) U V h hU hV = Proj.map ((𝒮).res h) hirr :=
    Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens
      (𝒮).toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h _
  rw [hmap]
  have := specMap_awayEvalOfEqOne_awayι_comp_map ((𝒮).grading V) (sectionLift f hV)
    (sectionLift_oneSection f hV) ((𝒮).res h) hirr (oneSection_mem f V) (oneSection_mem f U)
    (res_oneSection f h) (sectionLift f hU) (sectionLift_oneSection f hU)
    (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom (sectionLift_res f hU hV h)
  exact (Category.assoc _ _ _).trans this

theorem sectionLift_strHom {V : S.Opens} (hV : IsAffineOpen V) (r : Γ(S, V)) :
    sectionLift f hV ((𝒮).strHom V r) = f.app V r := by
  rw [(𝒮).strHom_apply, sectionLift_of]
  have hone : (r • (𝒮).one V : (𝒮).sectionPieces V 0) = symPieceAddEquiv f hV 0
      (r • Stacks.SymGraded.oneG (R := Γ(S, V)) Γ(structurePushforward f, V)) :=
    (((PresheafOfModules.sheafifyUnit (R := S.ringCatSheaf) (𝟙 S.ringCatSheaf.obj)
      (Stacks.SymGraded.siteGradedPiece (structurePushforward f).val 0)).app (op V)).hom.map_smul
        r _).symm
  rw [hone]
  refine (pieceLift_unit f hV 0 _).trans ?_
  exact (congrArg (symLift f V) (Algebra.algebraMap_eq_smul_one r).symm).trans
    (symLift_algebraMap f V r)

/-- **The chart morphism lies over the base.** -/
theorem chartEmbedding_comp_toOpen {V : S.Opens} (hV : IsAffineOpen V) :
    chartEmbedding f hV ≫ projInclusionToOpen (𝒮) V hV ≫ V.ι =
      Spec.map (f.app V) ≫ hV.fromSpec := by
  change chartEmbedding f hV ≫ (Proj.toSpecZero ((𝒮).grading V) ≫
    Spec.map ((𝒮).toGradedAlgebra.strZero (⟨V, hV⟩ : S.AffineZariskiSite)) ≫ hV.isoSpec.inv) ≫
      V.ι = _
  rw [Category.assoc, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, chartEmbedding, Category.assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp_assoc]
  refine (Spec.map_comp_assoc _ _ _).symm.trans
    (congrArg (fun g => Spec.map g ≫ hV.fromSpec) ?_)
  ext r
  exact (awayEvalOfEqOne_fromZeroRingHom ((𝒮).grading V) (sectionLift f hV)
    (sectionLift_oneSection f hV) _).trans ((congrArg (sectionLift f hV)
      (Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply
        (𝒮).toGradedAlgebra (⟨V, hV⟩ : S.AffineZariskiSite) r)).trans (sectionLift_strHom f hV r))

theorem chartEmbedding_comp_chart_comp_toBase {V : S.Opens} (hV : IsAffineOpen V) :
    chartEmbedding f hV ≫ (relativeProj (𝒮)).chart V hV ≫ (relativeProj (𝒮)).toBase =
      (hV.preimage f).fromSpec ≫ f := by
  rw [((relativeProj (𝒮)).chart_isPullback V hV).w, chartEmbedding_comp_toOpen,
    Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]

/-! ### Glueing -/

/-- The identification of the member of the pulled-back directed affine cover over an affine open
`U` of the base with `Spec Γ(X, f⁻¹(U))`. -/
def coverToSpec (U : S.affineOpens) : pullback f (U : S.Opens).ι ⟶ Spec Γ(X, f ⁻¹ᵁ U) :=
  (pullbackRestrictIsoRestrict f U).hom ≫ (U.2.preimage f).isoSpec.hom

@[reassoc]
theorem coverToSpec_fromSpec (U : S.affineOpens) :
    coverToSpec f U ≫ (U.2.preimage f).fromSpec = pullback.fst f (U : S.Opens).ι := by
  rw [coverToSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    pullbackRestrictIsoRestrict_hom_ι]

/-- The member over an affine open `U` of the base of the family that glues to the embedding. -/
def localEmbedding (U : S.affineOpens) :
    pullback f (U : S.Opens).ι ⟶ (relativeProj (𝒮)).scheme :=
  coverToSpec f U ≫ chartEmbedding f U.2 ≫ (relativeProj (𝒮)).chart U U.2

theorem pullbackMap_comp_coverToSpec {U V : S.affineOpens} (h : U ≤ V) :
    pullback.map f (U : S.Opens).ι f (V : S.Opens).ι (𝟙 _) (S.homOfLE h) (𝟙 _)
        (by simp) (by simp) ≫ coverToSpec f V =
      coverToSpec f U ≫ Spec.map (X.presheaf.map (homOfLE (f.preimage_mono h)).op) := by
  rw [← cancel_mono (V.2.preimage f).fromSpec, Category.assoc, Category.assoc,
    coverToSpec_fromSpec, IsAffineOpen.map_fromSpec _ (U.2.preimage f), coverToSpec_fromSpec,
    pullback.lift_fst, Category.comp_id]

theorem localEmbedding_compat {U V : S.affineOpens} (h : U ≤ V) :
    pullback.map f (U : S.Opens).ι f (V : S.Opens).ι (𝟙 _) (S.homOfLE h) (𝟙 _)
        (by simp) (by simp) ≫ localEmbedding f V = localEmbedding f U := by
  rw [localEmbedding, reassoc_of% pullbackMap_comp_coverToSpec f h,
    ← chartEmbedding_comp_projInclusionMap_assoc f U.2 V.2 h,
    (relativeProj (𝒮)).chart_transition U V h U.2 V.2]
  rfl

theorem trans_localEmbedding {U V : (S.directedAffineCover.pullback₁ f).I₀} (hUV : U ⟶ V) :
    Scheme.Cover.trans (S.directedAffineCover.pullback₁ f) hUV ≫ localEmbedding f V =
      localEmbedding f U :=
  localEmbedding_compat f (leOfHom hUV)

/-- **The embedding `X ⟶ 𝐏(f_*𝒪_X)`**: the glueing of the chart morphisms along the directed
cover of `X` by the inverse images of the affine opens of the base. -/
def embedding : X ⟶ (relativeProj (𝒮)).scheme :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected (S.directedAffineCover.pullback₁ f)
    (fun U => localEmbedding f U) (trans_localEmbedding f)

theorem pullbackFst_embedding (U : S.affineOpens) :
    pullback.fst f (U : S.Opens).ι ≫ embedding f = localEmbedding f U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (S.directedAffineCover.pullback₁ f) _
    (trans_localEmbedding f) U

/-- **The embedding is a morphism over the base.** -/
@[reassoc]
theorem embedding_comp_toBase : embedding f ≫ (relativeProj (𝒮)).toBase = f := by
  refine Scheme.Cover.hom_ext (S.directedAffineCover.pullback₁ f) _ _ fun (U : S.affineOpens) => ?_
  change pullback.fst f (U : S.Opens).ι ≫ _ = pullback.fst f (U : S.Opens).ι ≫ f
  rw [← Category.assoc, pullbackFst_embedding, localEmbedding]
  simp only [Category.assoc]
  exact (congrArg (coverToSpec f U ≫ ·) (chartEmbedding_comp_chart_comp_toBase f U.2)).trans
    (coverToSpec_fromSpec_assoc f U f)

theorem chartEmbedding_comp_toOpen_ι {V : S.Opens} (hV : IsAffineOpen V) :
    chartEmbedding f hV ≫ projInclusionToOpen (𝒮) V hV ≫ V.ι = (hV.preimage f).fromSpec ≫ f := by
  rw [chartEmbedding_comp_toOpen, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec f hV (hV.preimage f)]

/-- **Over the chart of an affine open `U` of the base, the embedding is the chart morphism**:
the inverse image of the chart `Proj Γ(U, Sym(f_*𝒪_X))` under the embedding is `f⁻¹(U)`, mapped
by the chart morphism. -/
theorem isPullback_chart (U : S.affineOpens) :
    IsPullback (pullback.fst f (U : S.Opens).ι) (coverToSpec f U ≫ chartEmbedding f U.2)
      (embedding f) ((relativeProj (𝒮)).chart U U.2) := by
  have hsnd : (coverToSpec f U ≫ chartEmbedding f U.2) ≫ projInclusionToOpen (𝒮) U U.2 =
      pullback.snd f (U : S.Opens).ι := by
    rw [← cancel_mono (U : S.Opens).ι, Category.assoc, Category.assoc]
    refine (congrArg (coverToSpec f U ≫ ·) (chartEmbedding_comp_toOpen_ι f U.2)).trans ?_
    rw [coverToSpec_fromSpec_assoc, pullback.condition]
  refine IsPullback.of_bot ?_ (by rw [pullbackFst_embedding, localEmbedding, Category.assoc])
    ((relativeProj (𝒮)).chart_isPullback U U.2)
  rw [hsnd, embedding_comp_toBase]
  exact IsPullback.of_hasPullback f (U : S.Opens).ι

/-- **The embedding is an immersion**, since it is one over each chart of the target. -/
theorem isImmersion_embedding : IsImmersion (embedding f) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen S =>
      ((relativeProj (𝒮)).chart U.1 U.2).opensRange)
    (Stacks.AlgebraicGeometry.ProjBundleSurjection.iSup_opensRange_chart_eq_top
      (relativeProj (𝒮))) fun U => ?_
  have h₂ := isPullback_chart f ⟨U.1, U.2⟩
  have h₁ : IsPullback (pullback.fst (embedding f) ((relativeProj (𝒮)).chart U.1 U.2))
      (pullback.snd (embedding f) ((relativeProj (𝒮)).chart U.1 U.2)) (embedding f)
      ((relativeProj (𝒮)).chart U.1 U.2) := IsPullback.of_hasPullback _ _
  have e₁ : Arrow.mk (coverToSpec f ⟨U.1, U.2⟩ ≫ chartEmbedding f U.2) ≅
      Arrow.mk (pullback.snd (embedding f) ((relativeProj (𝒮)).chart U.1 U.2)) :=
    Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _)
  have e₂ := morphismRestrictOpensRange (embedding f) ((relativeProj (𝒮)).chart U.1 U.2)
  have : IsImmersion (chartEmbedding f U.2) := isImmersion_chartEmbedding f U.2
  have : IsImmersion (coverToSpec f ⟨U.1, U.2⟩ ≫ chartEmbedding f U.2) := by
    rw [coverToSpec, Category.assoc]; infer_instance
  have hw := Arrow.inv_left_hom_right (e₁.trans e₂.symm).hom
  simp only [Arrow.mk_hom] at hw
  rw [← hw]
  infer_instance

/-- **For a finite morphism the embedding `X ⟶ 𝐏(f_*𝒪_X)` is a closed immersion.** It is an
immersion over the separated projection of the projective bundle (Tag 01OD), and its composite with
that projection is the finite morphism `f`. -/
theorem isClosedImmersion_embedding [IsFinite f] : IsClosedImmersion (embedding f) := by
  have := isImmersion_embedding f
  have : IsSeparated (relativeProj (𝒮)).toBase :=
    Stacks.SymGraded.isSeparated_projectiveBundleToBase (structurePushforward f)
  exact isClosedImmersion_of_isImmersion_of_eq _ _ (embedding_comp_toBase f)

end Stacks.FiniteMorphismProjective

end
