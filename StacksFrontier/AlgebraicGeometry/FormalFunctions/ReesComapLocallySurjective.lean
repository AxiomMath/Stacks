module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing

/-!
# The Rees comparison `ψ` is locally surjective

Let `g : Z ⟶ Y` be a morphism of schemes with `Y` **affine** and let `K` be a quasi-coherent sheaf
of ideals on `Y`. `Stacks.Blowup.reesComapPullbackHom` is the adjoint transpose

`ψ : g^*(⨁ₙ Kⁿ) ⟶ ⨁ₙ (K𝒪_Z)ⁿ`

of the degreewise inverse image of [Stacks, Tag 01OG], a morphism of sheaves of commutative
`𝒪_Z`-algebras out of the **algebra** pullback. This file proves that its morphism of sheaves of
rings is **locally surjective**, which is the last datum of [Stacks, Tag 0897]'s base change that
[Stacks, Tag 02O8] consumed as a hypothesis through
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isLocallySurjective`.

## Main results

* `Stacks.Blowup.isLocallySurjective_reesComapPullbackHom`: **`ψ` is locally surjective**, for an
  arbitrary `g` into an affine base, and
  `Stacks.Blowup.surjective_reesComapPullbackHom_right_app_of_isAffineOpen`: it is in fact
  surjective on the sections over every affine open.
* `Stacks.Cohomology.FormalFunctions.isLocallySurjective_baseReesComapPullbackHom`: the same for
  `ψ : f^* B̃ ⟶ ⨁_{n ≥ 0} ℐⁿ` at `f : X ⟶ Spec A` and `K = Ĩ`.
* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isCoherent`:
  **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module with the whole geometry of the
  base change discharged** — only the coherence of `F'` and the `B`-linear comparison `cmp`
  remain as hypotheses. Coherence of `F'` is now proved too, in
  `StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesBaseChangeCoherent`, so the form of `h0897`
  with `cmp` as its only remaining hypothesis is
  `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_cmp` there.

## Implementation notes

The only handle on `ψ` is `Stacks.Blowup.reesComapPullbackHom_app_unit`: on the unit image of a
global section of `⨁ₙ Kⁿ` it is `β`, the degreewise inverse image assembled on global sections.
So the proof is a generation argument, run over an affine open `V` of `Z` inside the subring

`Stacks.Blowup.reesComapImage g K V`, the image of `ψ` on the sections over `V`.

That subring contains the image of the structure map of `⨁ₙ (K𝒪_Z)ⁿ`
(`Stacks.Blowup.mem_reesComapImage_structureMap`, which is nothing but `CategoryTheory.Under.w`
for `ψ`), hence is a `Γ(Z, V)`-submodule, and it contains the restriction of the inverse image of
every global homogeneous section (`Stacks.Blowup.mem_reesComapImage_comap_restrict`). Three steps
then close it:

* over an affine open the sections of `⨁ₙ (K𝒪_Z)ⁿ` are the direct sum of the sections of the
  homogeneous pieces (`Stacks.RelativeSpec.totalSectionsRingEquiv`), and a section of that direct
  sum is a *finite* sum of homogeneous ones (`Stacks.GradedAlgebra.incl_induction`), so only
  homogeneous sections have to be reached — `Stacks.Blowup.mem_reesComapImage_totalUnit`;
* a homogeneous section in nonnegative degree is determined by its ambient section in `Γ(Z, V)`
  (`Stacks.Blowup.reesPieceAmbient_injective`), and the ambient sections of the degree-`n` piece
  over an affine `V` are exactly `((K𝒪_Z)(V))ⁿ = ((K(⊤))ⁿ) · Γ(Z, V)`
  (`Stacks.Blowup.reesPieceAmbient_mem_affine` with `Stacks.IdealSheaf.ideal_comap_appLE` and
  `Ideal.map_pow`), the base `Y` being affine so that `⊤` serves as the chart downstairs;
* that ideal is by definition a span, so `Submodule.span_induction` reduces the whole statement to
  its generators — `Stacks.Blowup.exists_mem_reesComapImage_of_mem_map`. A generator is
  `g.appLE ⊤ V a` for `a ∈ (K(⊤))ⁿ`, which is the ambient section of the restricted inverse image
  of the global homogeneous section `Stacks.Blowup.reesPieceAffineEquiv` attaches to `a`.

In a negative degree the homogeneous piece is a zero object
(`Stacks.Blowup.reesPiece_negative_isZero`) and there is nothing to reach.

**Why `Stacks.sectionRestrict` and not the restriction map itself.** The codomain of
`(reesPiece L n).val.map f` is written as a `ModuleCat.restrictScalars`, so
`ConcreteCategory.hom ((reesPiece L n).val.map f) x` does not have the type
`(reesPiece L n).val.obj (op V)` that `SheafOfModules.GradedAlgebra.ungradedIncl` asks for;
`Stacks.sectionRestrict` is the same function with its target type written in the latter
spelling, and every statement below uses it. This is the `ModuleCat.restrictScalars` instance
diamond.

No `@[stacks]` attribute is attached: local surjectivity of `ψ` is not the assertion of a tag, it
is the input [Stacks, Tag 0897]'s base change needs. In particular [Stacks, Tag 0G7X] is *not*
registered anywhere on the strength of this file: the chain through
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isCoherent` is still
conditional on two hypotheses.

## What remains for `h0897`

**Exactly one hypothesis: `cmp`,** the `B`-linear comparison
`⨁ₙ Hᵖ(X, Mₙ) ≃ₗ[B] Hᵖ(X', F')` — item 3 of the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange`.

The other hypothesis of
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isCoherent`,
`[F'.IsCoherent]`, is **discharged**:
`Stacks.Cohomology.FormalFunctions.isCoherent_reesBaseChangeModule` in
`StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesBaseChangeCoherent`. It rests on the
`𝓐`-analogue of [Stacks, Tag 01PB]
(`Stacks.AlgebraicGeometry.QcohOverAlgebra.module_finite_sections_of_generatesLocally`) and on
the transport of finite type across [Stacks, Tag 01SB]
(`Stacks.AffineAlgebraEquivalence.isFiniteType_inverse_obj`), both of which were absent and are
now proved.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Blowup Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.Blowup

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) (K : Y.IdealSheafData) [IsAffine Y]

/-- The global-sections comparison `reesComapSections` carries the inclusion into `⨁ₙ Kⁿ` of a
global section `x` of `Kⁿ` to the inclusion into `⨁ₙ (K𝒪_Z)ⁿ` of its image under the degreewise
inverse image `Kⁿ ⟶ g_*(K𝒪_Z)ⁿ`. -/
theorem reesComapSections_ungradedIncl (n : ℤ)
    (x : (reesPiece K n).val.obj (op (⊤ : Y.Opens))) :
    reesComapSections g K ((reesGradedAlgebra K).ungradedIncl n x) =
      (reesGradedAlgebra (K.comap g)).ungradedIncl n
        ((reesPieceComap g K n).val.app (op ⊤) x) := by
  have h : (Stacks.RelativeSpec.totalSectionsRingEquiv Y (reesGradedAlgebra K)
        (fun i j W a b => reesMultiplication_comm K i j W a b)
        (isAffineOpen_top Y)).symm ((reesGradedAlgebra K).ungradedIncl n x) =
      (reesGradedAlgebra K).toPresheafGradedAlgebra.incl n x :=
    (Stacks.RelativeSpec.totalSectionsRingEquiv Y (reesGradedAlgebra K)
        (fun i j W a b => reesMultiplication_comm K i j W a b)
        (isAffineOpen_top Y)).symm_apply_apply _
  exact (congrArg (reesComapTotalHom g K ⊤) h).trans (reesComapTotalHom_incl g K ⊤ n x)

/-- The image of `ψ` on the sections over an open, as a subring of the sections of `⨁ₙ (K𝒪_Z)ⁿ`. -/
def reesComapImage (V : Z.Opens) :
    Subring ↥(AlgebraSheaf.sections (reesAlgebraSheaf (K.comap g)) V) :=
  RingHom.range ((reesComapPullbackHom g K).right.hom.app (op V)).hom

/-- The image of `ψ` over `V` contains the image of the structure map `𝒪_Z ⟶ ⨁ₙ (K𝒪_Z)ⁿ`, since
`ψ` is a morphism of `𝒪_Z`-algebras. -/
theorem mem_reesComapImage_structureMap (V : Z.Opens)
    (r : Z.ringCatSheaf.obj.obj (op V)) :
    ((reesGradedAlgebra (K.comap g)).ungradedStructureMap.hom.app (op V)).hom r ∈
      reesComapImage g K V := by
  refine ⟨ConcreteCategory.hom
      (((algebraPullback g).obj (reesAlgebraSheaf K)).hom.hom.app (op V)) r, ?_⟩
  exact congrArg (fun φ : Z.sheaf ⟶ (reesAlgebraSheaf (K.comap g)).right =>
      ConcreteCategory.hom (φ.hom.app (op V)) r) (Under.w (reesComapPullbackHom g K))

/-- **A global homogeneous section of `⨁ₙ Kⁿ` is carried by `ψ` into the image over `g⁻¹⊤`.**
This is `Stacks.Blowup.reesComapPullbackHom_app_unit` read through
`Stacks.Blowup.reesComapSections_ungradedIncl`. -/
theorem mem_reesComapImage_comap (n : ℤ) (x : (reesPiece K n).val.obj (op (⊤ : Y.Opens))) :
    (reesGradedAlgebra (K.comap g)).ungradedIncl n
        ((reesPieceComap g K n).val.app (op ⊤) x) ∈
      reesComapImage g K (g ⁻¹ᵁ (⊤ : Y.Opens)) :=
  ⟨_, (reesComapPullbackHom_app_unit g K ((reesGradedAlgebra K).ungradedIncl n x)).trans
    (reesComapSections_ungradedIncl g K n x)⟩

/-- The image of `ψ` is compatible with restriction: the restriction of a section in the image
over an open is in the image over any smaller open. -/
theorem mem_reesComapImage_of_le {V W : Z.Opens} (h : V ≤ W)
    {t : ↥(AlgebraSheaf.sections (reesAlgebraSheaf (K.comap g)) W)}
    (ht : t ∈ reesComapImage g K W) :
    ConcreteCategory.hom ((reesAlgebraSheaf (K.comap g)).right.obj.map (homOfLE h).op) t ∈
      reesComapImage g K V := by
  obtain ⟨u, hu⟩ := ht
  refine ⟨ConcreteCategory.hom
    (((algebraPullback g).obj (reesAlgebraSheaf K)).right.obj.map (homOfLE h).op) u, ?_⟩
  refine Eq.trans
    (NatTrans.naturality_apply (reesComapPullbackHom g K).right.hom (homOfLE h).op u) ?_
  exact congrArg (fun z => ConcreteCategory.hom
    ((reesAlgebraSheaf (K.comap g)).right.obj.map (homOfLE h).op) z) hu

/-- **The restriction to a smaller open of a global homogeneous section's image is in the image.**
`Stacks.Blowup.mem_reesComapImage_comap` read through the naturality of the degree-`n` inclusion
into the ungraded realization. -/
theorem mem_reesComapImage_comap_restrict {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) (n : ℤ)
    (x : (reesPiece K n).val.obj (op (⊤ : Y.Opens))) :
    (reesGradedAlgebra (K.comap g)).ungradedIncl n
        (Stacks.sectionRestrict (reesPiece (K.comap g) n).val (homOfLE hV).op
          ((reesPieceComap g K n).val.app (op ⊤) x)) ∈
      reesComapImage g K V := by
  obtain ⟨u, hu⟩ := mem_reesComapImage_of_le g K hV (mem_reesComapImage_comap g K n x)
  exact ⟨u, hu.trans ((reesGradedAlgebra (K.comap g)).ungradedIncl_naturality
    (homOfLE hV).op n ((reesPieceComap g K n).val.app (op ⊤) x))⟩

omit [IsAffine Y] in
/-- **The ambient section of a global homogeneous section's restriction is the image of its own
ambient section under the restricted map of sections `g.appLE`.** -/
theorem reesPieceAmbient_comap_restrict {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) (n : ℤ)
    (x : (reesPiece K n).val.obj (op (⊤ : Y.Opens))) :
    reesPieceAmbient (K.comap g) n V
        (Stacks.sectionRestrict (reesPiece (K.comap g) n).val (homOfLE hV).op
          ((reesPieceComap g K n).val.app (op ⊤) x)) =
      (g.appLE (⊤ : Y.Opens) V hV).hom (reesPieceAmbient K n ⊤ x) :=
  (reesPieceAmbient_restrict (K.comap g) n V (g ⁻¹ᵁ (⊤ : Y.Opens)) hV _).trans
    (congrArg (ConcreteCategory.hom (Z.presheaf.map (homOfLE hV).op))
      (reesPieceAmbient_comap g K n ⊤ x))

/-- Transport membership in the image of `ψ` along an equality of sections. -/
theorem mem_reesComapImage_congr {V : Z.Opens}
    {a b : (reesGradedAlgebra (K.comap g)).ungradedSheaf.obj.obj (op V)} (h : a = b)
    (ha : a ∈ reesComapImage g K V) : b ∈ reesComapImage g K V := h ▸ ha

/-- The zero section of a homogeneous piece is in the image of `ψ`. -/
private theorem mem_reesComapImage_ungradedIncl_zero (n : ℤ) (V : Z.Opens) :
    (reesGradedAlgebra (K.comap g)).ungradedIncl n
      (0 : (reesPiece (K.comap g) n).val.obj (op V)) ∈ reesComapImage g K V :=
  mem_reesComapImage_congr g K
    (Stacks.GradedAlgebra.inclSheaf_zero
      (reesGradedAlgebra (K.comap g)).toPresheafGradedAlgebra _ n).symm
    (reesComapImage g K V).zero_mem

/-- **Every ambient section in the extension of `(K(⊤))ⁿ` along `g.appLE` is the ambient section
of a degree-`n` section whose image in the ungraded realization lies in the image of `ψ`.**

This is the generation step, and it is an induction over the span defining `Ideal.map`: a
generator `g.appLE ⊤ V hV a` with `a ∈ (K(⊤))ⁿ` comes from a global homogeneous section of
`⨁ₙ Kⁿ` (`Stacks.Blowup.reesPieceAffineEquiv` over the affine `Y`) whose restricted inverse image
has exactly that ambient section (`Stacks.Blowup.reesPieceAmbient_comap_restrict`) and is in the
image (`Stacks.Blowup.mem_reesComapImage_comap_restrict`); sums are handled because the image is
a subring and `Stacks.Blowup.reesPieceAmbient` is additive; and a scalar multiple is handled
because the image contains the image of the structure map
(`Stacks.Blowup.mem_reesComapImage_structureMap`), so it is a `Γ(Z, V)`-submodule. -/
theorem exists_mem_reesComapImage_of_mem_map (n : ℤ) (hn : 0 ≤ n) {V : Z.Opens}
    (hV : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) {c : Γ(Z, V)}
    (hc : c ∈ Ideal.map (g.appLE (⊤ : Y.Opens) V hV).hom
      (K.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n.toNat)) :
    ∃ x' : (reesPiece (K.comap g) n).val.obj (op V),
      reesPieceAmbient (K.comap g) n V x' = c ∧
      (reesGradedAlgebra (K.comap g)).ungradedIncl n x' ∈ reesComapImage g K V := by
  refine Submodule.span_induction
    (p := fun c _ => ∃ x' : (reesPiece (K.comap g) n).val.obj (op V),
      reesPieceAmbient (K.comap g) n V x' = c ∧
      (reesGradedAlgebra (K.comap g)).ungradedIncl n x' ∈ reesComapImage g K V)
    ?_ ?_ ?_ ?_ hc
  · rintro t ⟨a, ha, rfl⟩
    refine ⟨Stacks.sectionRestrict (reesPiece (K.comap g) n).val (homOfLE hV).op
        ((reesPieceComap g K n).val.app (op ⊤)
          ((reesPieceAffineEquiv K n hn ⟨⊤, isAffineOpen_top Y⟩).symm ⟨a, ha⟩)), ?_,
      mem_reesComapImage_comap_restrict g K hV n _⟩
    refine (reesPieceAmbient_comap_restrict g K hV n _).trans ?_
    refine congrArg (ConcreteCategory.hom (g.appLE (⊤ : Y.Opens) V hV)) ?_
    refine (reesPieceAffineEquiv_coe K n hn ⟨⊤, isAffineOpen_top Y⟩ _).symm.trans ?_
    exact congrArg (fun z : ↥(K.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n.toNat) => (z : Γ(Y, ⊤)))
      ((reesPieceAffineEquiv K n hn ⟨⊤, isAffineOpen_top Y⟩).apply_symm_apply ⟨a, ha⟩)
  · exact ⟨0, reesPieceAmbient_zero (K.comap g) n V,
      mem_reesComapImage_ungradedIncl_zero g K n V⟩
  · rintro c₁ c₂ - - ⟨x₁, hx₁, hm₁⟩ ⟨x₂, hx₂, hm₂⟩
    refine ⟨x₁ + x₂, (reesPieceAmbient_add (K.comap g) n V x₁ x₂).trans
      (congrArg₂ (· + ·) hx₁ hx₂), ?_⟩
    exact mem_reesComapImage_congr g K
      ((reesGradedAlgebra (K.comap g)).ungradedIncl_add n (op V) x₁ x₂).symm
      ((reesComapImage g K V).add_mem hm₁ hm₂)
  · rintro a c₁ - ⟨x₁, hx₁, hm₁⟩
    refine ⟨(show Z.ringCatSheaf.obj.obj (op V) from a) • x₁, ?_, ?_⟩
    · exact (reesPieceAmbient_smul (K.comap g) n V _ x₁).trans
        (congrArg (fun t => (a : Γ(Z, V)) * t) hx₁)
    · exact mem_reesComapImage_congr g K
        ((reesGradedAlgebra (K.comap g)).ungradedIncl_smul n (op V) _ x₁).symm
        ((reesComapImage g K V).mul_mem
          (mem_reesComapImage_structureMap g K V _) hm₁)

/-- **Every homogeneous section over an affine open is in the image of `ψ`.**

In a negative degree the homogeneous piece is a zero object
(`Stacks.Blowup.reesPiece_negative_isZero`), so the section is zero. In a nonnegative degree its
ambient section lies in `((K𝒪_Z)(V))ⁿ = ((K(⊤))ⁿ · Γ(Z, V))`
(`Stacks.Blowup.reesPieceAmbient_mem_affine` and `Stacks.IdealSheaf.ideal_comap_appLE`), so
`Stacks.Blowup.exists_mem_reesComapImage_of_mem_map` produces a section in the image with the
same ambient section, and a homogeneous section in nonnegative degree is determined by its
ambient section. -/
theorem mem_reesComapImage_ungradedIncl {V : Z.Opens} (hV : IsAffineOpen V) (n : ℤ)
    (x : (reesPiece (K.comap g) n).val.obj (op V)) :
    (reesGradedAlgebra (K.comap g)).ungradedIncl n x ∈ reesComapImage g K V := by
  rcases lt_or_ge n 0 with hn | hn
  · have hsub : Subsingleton ↥((reesPiece (K.comap g) n).val.obj (op V)) :=
      Stacks.subsingleton_of_isZero (reesPiece_negative_isZero (K.comap g) n hn) (op V)
    obtain rfl : x = 0 := Subsingleton.elim _ _
    exact mem_reesComapImage_ungradedIncl_zero g K n V
  · have hVtop : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := le_top
    have heq : (K.comap g).ideal ⟨V, hV⟩ ^ n.toNat =
        Ideal.map (g.appLE (⊤ : Y.Opens) V hVtop).hom
          (K.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n.toNat) :=
      (congrArg (· ^ n.toNat)
          (Stacks.IdealSheaf.ideal_comap_appLE K g ⟨⊤, isAffineOpen_top Y⟩ ⟨V, hV⟩ hVtop)).trans
        (Ideal.map_pow _ _ _).symm
    obtain ⟨x', hx', hm'⟩ := exists_mem_reesComapImage_of_mem_map g K n hn hVtop
      (heq ▸ reesPieceAmbient_mem_affine (K.comap g) n hn ⟨V, hV⟩ x)
    exact mem_reesComapImage_congr g K
      (congrArg ((reesGradedAlgebra (K.comap g)).ungradedIncl n)
        (reesPieceAmbient_injective (K.comap g) n hn V hx')) hm'

/-- **Every section of the direct sum of the homogeneous sections over an affine open is in the
image of `ψ`**: a section of the presheaf direct sum is a *finite* sum of homogeneous ones
(`Stacks.GradedAlgebra.incl_induction`) and the image is a subring. -/
theorem mem_reesComapImage_totalUnit {V : Z.Opens} (hV : IsAffineOpen V)
    (a : (reesGradedAlgebra (K.comap g)).toPresheafGradedAlgebra.Total (op V)) :
    (reesGradedAlgebra (K.comap g)).toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (Z : TopCat)) (op V) a ∈ reesComapImage g K V := by
  induction a using (reesGradedAlgebra (K.comap g)).toPresheafGradedAlgebra.incl_induction with
  | zero => exact mem_reesComapImage_congr g K (map_zero _).symm (reesComapImage g K V).zero_mem
  | incl n x => exact mem_reesComapImage_ungradedIncl g K hV n x
  | add a a' ha ha' =>
      exact mem_reesComapImage_congr g K (map_add _ a a').symm
        ((reesComapImage g K V).add_mem ha ha')

/-- **`ψ` is surjective on the sections over an affine open.** Over an affine open the sections
of `⨁ₙ (K𝒪_Z)ⁿ` are the direct sum of the sections of the homogeneous pieces
(`Stacks.RelativeSpec.totalSectionsRingEquiv`), and every such section is in the image. -/
theorem surjective_reesComapPullbackHom_right_app_of_isAffineOpen {V : Z.Opens}
    (hV : IsAffineOpen V) :
    Function.Surjective
      (ConcreteCategory.hom ((reesComapPullbackHom g K).right.hom.app (op V))) := by
  intro s
  refine RingHom.mem_range.mp ?_
  refine Eq.mp (congrArg (fun z => z ∈ reesComapImage g K V) ?_)
    (mem_reesComapImage_totalUnit g K hV
      ((Stacks.RelativeSpec.totalSectionsRingEquiv Z (reesGradedAlgebra (K.comap g))
        (fun i j W a b => reesMultiplication_comm (K.comap g) i j W a b) hV).symm s))
  exact (Stacks.RelativeSpec.totalSectionsRingEquiv Z (reesGradedAlgebra (K.comap g))
    (fun i j W a b => reesMultiplication_comm (K.comap g) i j W a b) hV).apply_symm_apply s

/-- **`ψ : g^*(⨁ₙ Kⁿ) ⟶ ⨁ₙ (K𝒪_Z)ⁿ` is locally surjective**, for an arbitrary `g : Z ⟶ Y` into
an affine base.

This is the datum [Stacks, Tag 02O8]'s base change was missing: the affine opens below an open
generate a covering sieve of it (`AlgebraicGeometry.generate_affineOpensPresieve_mem`) and `ψ` is
surjective on the sections over each of them. -/
theorem isLocallySurjective_reesComapPullbackHom :
    CategoryTheory.Sheaf.IsLocallySurjective (reesComapPullbackHom g K).right := by
  refine ⟨fun {W} s => ?_⟩
  refine (Opens.grothendieckTopology (Z : TopCat)).superset_covering
      ((Sieve.generate_le_iff _ _).2 ?_) (generate_affineOpensPresieve_mem Z W)
  intro V i hV
  exact surjective_reesComapPullbackHom_right_app_of_isAffineOpen g K hV
    (ConcreteCategory.hom ((reesAlgebraSheaf (K.comap g)).right.obj.map i.op) s)

/-- The same for `ψ` with its target read along an equality identifying a sheaf of ideals on `Z`
with the inverse image of `K`: substitute the equality away. -/
theorem isLocallySurjective_reesComapPullbackHomOfEq {L : Z.IdealSheafData} (h : L = K.comap g) :
    CategoryTheory.Sheaf.IsLocallySurjective
      (h ▸ reesComapPullbackHom g K :
        (algebraPullback g).obj (reesAlgebraSheaf K) ⟶ reesAlgebraSheaf L).right := by
  subst h
  exact isLocallySurjective_reesComapPullbackHom g K

end Stacks.Blowup

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- **`ψ : f^* B̃ ⟶ ⨁_{n ≥ 0} ℐⁿ` is locally surjective**, for an arbitrary `f : X ⟶ Spec A`.

This is the last remaining datum of the base change of [Stacks, Tag 0897] that
[Stacks, Tag 02O8] consumes through
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_algebraPullbackHom`:
the base `Spec A` is affine, so
`Stacks.Blowup.isLocallySurjective_reesComapPullbackHom` applies to it. -/
theorem isLocallySurjective_baseReesComapPullbackHom :
    CategoryTheory.Sheaf.IsLocallySurjective (baseReesComapPullbackHom I X).right :=
  Stacks.Blowup.isLocallySurjective_reesComapPullbackHomOfEq X.hom (specIdealSheaf I)
    (baseIdealSheaf_eq_comap_specIdealSheaf I X)

attribute [local instance] cohomologyGradedModule

/-- **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module, with the whole geometry of
[Stacks, Tag 0897]'s base change discharged.**

Same statement as
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isLocallySurjective`
with its local-surjectivity hypothesis supplied by
`Stacks.Cohomology.FormalFunctions.isLocallySurjective_baseReesComapPullbackHom`. What is left
beyond [Stacks, Tag 0897]'s own hypotheses is the coherence of `F'` and the `B`-linear comparison
`cmp`; the closed immersion `X' ⟶ Spec(B) ×_{Spec A} X` and the morphism of algebra sheaves it
comes from are no longer hypotheses. -/
theorem isCohomologyReesFiniteOfGradedModule_of_isCoherent [IsNoetherianRing A]
    (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X)) (p : ℕ)
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))
    (F' : (reesRelativeSpec I X).left.Modules) [F'.IsCoherent]
    (cmp :
      letI := gradedCohomologySumModuleRees I X M p hneg
      gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I)
            (reesRelativeSpecToPullback I X (baseReesComapPullbackHom I X) ≫
              pullback.fst (reesSpecToBase I) X.hom))).obj
          (cohomologyOf (reesRelativeSpec I X).left p F'))) :
    IsCohomologyReesFiniteOfGradedModule I X M p :=
  isCohomologyReesFiniteOfGradedModule_of_isLocallySurjective I X M p hX hqc hft hneg
    (isLocallySurjective_baseReesComapPullbackHom I X) F' cmp

end Stacks.Cohomology.FormalFunctions

end
