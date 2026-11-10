module

public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackBaseAlgebra

/-!
# `ψ : f^* 𝔅 ⟶ 𝓐` is locally surjective for `𝓑 = f^* B̃`

`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSections.isProper_structureHom`
produces the proper structure morphism `f' : X' ⟶ Spec B` of [Stacks, Tag 0897]'s base change
from the local surjectivity of `ψ : f^* 𝔅 ⟶ 𝓐`, where `𝔅 = g_* 𝒪_{Spec B}` and `𝓐` is the
ungraded realization of the sheaf of graded algebras. **This file proves it for `𝓑 = f^* B̃`**,
and with it the properness of `f'` with nothing assumed beyond [Stacks, Tag 0897]'s own
hypothesis that `f` is proper.

## The generation argument

The image of `ψ` on the sections over an open `V` is a subring
`Stacks.AlgebraicGeometry.GradedProperCohomology.psiImage` of `Γ(𝓐, V)`. It contains the image of
the structure map of `𝓐` (that is `CategoryTheory.Under.w` for `ψ`), hence is a
`Γ(X, V)`-submodule, and it contains the restriction to `V` of the global section of `𝓑ₖ` named
by every homogeneous `b ∈ 𝒜ₖ` (that is `HomogeneousSections.basePullbackHom_app_unit`). Over an
**affine** open `V` that is already everything:

* a section of `𝓑ₖ = f^*(B̃ₖ)` over `V` is a `Γ(X, V)`-linear combination of pullbacks of global
  sections of `B̃ₖ`, because the sections of a pullback over a compatible pair of affine opens are
  the base change of the sections downstairs
  (`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, normalised by
  `affinePullbackSectionsBaseChangeIso_one_tmul`);
* a global section of `B̃ₖ` is named by a homogeneous element of degree `k`
  (`exists_specSection_eval_top`);
* in a negative degree the homogeneous piece of `f^* B̃` is a zero object;
* and the sections of `𝓐` over an affine open are the direct sum of the sections of the
  homogeneous pieces (`Stacks.RelativeSpec.totalSectionsRingEquiv`), each section of that direct
  sum being a finite sum of homogeneous ones (`Stacks.GradedAlgebra.incl_induction`).

Local surjectivity follows because the affine opens below an open generate a covering sieve of it
(`AlgebraicGeometry.generate_affineOpensPresieve_mem`).

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.pullbackBaseHom`: **`ψ : f^* 𝔅 ⟶ 𝓐`** for
  `𝓑 = f^* B̃`, with its structure-map compatibility supplied.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.pullbackStructureHom`: **`f' : X' ⟶ Spec B`.**

## Main results

* `isLocallySurjective_pullbackBaseHom`: **`ψ` is locally surjective.**
* `isProper_pullbackStructureHom`: **`f' : X' ⟶ Spec B` is proper.**

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum TensorProduct AlgebraicGeometry ChangeOfRings

universe u

namespace ModuleCat.ExtendScalars

/-- **A property of the elements of an extension of scalars which holds of the tensors `1 ⊗ m`
and is closed under addition and scalar multiples holds everywhere.** This is
`TensorProduct.inductionOn` for `ModuleCat.extendScalars`, stated for a general extension of
scalars: a tensor `s ⊗ m` is `s • (1 ⊗ m)` by `ModuleCat.ExtendScalars.smul_tmul`, and in the
general setting `mul_one` fires on the scalar ring itself rather than on a type whose
multiplication has been reached through a restriction of scalars. -/
public theorem forall_of_one_tmul {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M : ModuleCat.{u} R} (P : ((ModuleCat.extendScalars φ).obj M) → Prop)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (s : S) (x), P x → P (s • x))
    (hone : ∀ m : M, P ((1 : S) ⊗ₜ[R, φ] m)) : ∀ x, P x := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      have key : ∀ s' : S, P (s' ⊗ₜ[R, φ] m) := by
        intro s'
        have h := ModuleCat.ExtendScalars.smul_tmul (f := φ) s' (1 : S) m
        rw [mul_one] at h
        exact cast (congrArg P h) (hsmul s' _ (hone m))
      exact key s
  | add x y hx hy => exact hadd _ _ hx hy

end ModuleCat.ExtendScalars

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The image of `ψ`, for an arbitrary sheaf of graded algebras

Everything in this section is generic in the `GradedQcohAlgebra` and its homogeneous-sections
datum: the image of `ψ` is a `Γ(X, V)`-submodule containing the sections named by the homogeneous
elements, and that is all the local surjectivity argument uses — *except* the generation step,
which is isolated as `HasAffinePsiGeneration`. For `𝓑 = f^* B̃` that step is
`mem_psiImage_ungradedIncl_natDegree` below; for the associated graded algebra of an ideal sheaf
it is supplied by `Stacks.Coherent.span_range_affineGradedComparison_eq_top` through
`hasAffinePsiGeneration_of_span`. -/

section Generic

variable (D : GradedQcohAlgebra X) (S : HomogeneousSections D.alg 𝒜)
  (hsc : HomogeneousSections.IsStructureCompatible D S f)

/-- The image of `ψ` on the sections over an open, as a subring of the sections of `𝓐`. -/
def psiImage (V : X.Opens) : Subring ↥(AlgebraSheaf.sections D.sheaf V) :=
  RingHom.range
    ((HomogeneousSections.basePullbackHom D S f hsc).right.hom.app (op V)).hom

/-- Transport membership in the image of `ψ` along an equality of sections. -/
theorem mem_psiImage_congr {V : X.Opens}
    {a b : ↥(AlgebraSheaf.sections D.sheaf V)} (h : a = b)
    (ha : a ∈ psiImage 𝒜 f D S hsc V) : b ∈ psiImage 𝒜 f D S hsc V := h ▸ ha

/-- **The image of `ψ` contains the image of the structure map of `𝓐`**, so it is a
`Γ(X, V)`-submodule and not merely a subring. This is `CategoryTheory.Under.w` for `ψ`. -/
theorem mem_psiImage_structureMap (V : X.Opens) (r : X.ringCatSheaf.obj.obj (op V)) :
    (D.alg.ungradedStructureMap.hom.app (op V)).hom r ∈ psiImage 𝒜 f D S hsc V := by
  refine ⟨ConcreteCategory.hom
      ((((algebraPullback f).obj
        (pushforwardAlgebra (algebraSpecToBase A B))).hom.hom.app (op V))) r, ?_⟩
  exact congrArg (fun φ : X.sheaf ⟶ D.sheaf.right =>
      ConcreteCategory.hom (φ.hom.app (op V)) r)
    (Under.w (HomogeneousSections.basePullbackHom D S f hsc))

/-- The image of `ψ` is compatible with restriction. -/
theorem mem_psiImage_of_le {V W : X.Opens} (h : V ≤ W)
    {t : ↥(AlgebraSheaf.sections D.sheaf W)} (ht : t ∈ psiImage 𝒜 f D S hsc W) :
    ConcreteCategory.hom (D.sheaf.right.obj.map (homOfLE h).op) t ∈
      psiImage 𝒜 f D S hsc V := by
  obtain ⟨u, hu⟩ := ht
  refine ⟨ConcreteCategory.hom
    (((algebraPullback f).obj
      (pushforwardAlgebra (algebraSpecToBase A B))).right.obj.map (homOfLE h).op) u, ?_⟩
  refine Eq.trans
    (NatTrans.naturality_apply
      (HomogeneousSections.basePullbackHom D S f hsc).right.hom (homOfLE h).op u) ?_
  exact congrArg (fun z => ConcreteCategory.hom
    (D.sheaf.right.obj.map (homOfLE h).op) z) hu

/-- **The global section of `𝓑ₖ` named by a homogeneous element of degree `k` is in the image of
`ψ` over `f⁻¹⊤`.** This is `HomogeneousSections.basePullbackHom_app_unit` at the global section
of `𝔅` that the element names. -/
theorem mem_psiImage_secIncl_top {k : ℕ} (b : ↥(𝒜 k)) :
    HomogeneousSections.secIncl D S b (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))) ∈
      psiImage 𝒜 f D S hsc (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)) := by
  refine ⟨((algebraPullbackPushforwardAdjunction f).unit.app
      (pushforwardAlgebra (algebraSpecToBase A B))).right.hom.app (op ⊤)
    (show ↥(AlgebraSheaf.sections (pushforwardAlgebra (algebraSpecToBase A B)) ⊤) from
      (Scheme.ΓSpecIso (.of B)).inv.hom (b : B)), ?_⟩
  refine Eq.trans (HomogeneousSections.basePullbackHom_app_unit D S f hsc _) ?_
  change HomogeneousSections.secRingHom D S (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens)))
      ((Scheme.ΓSpecIso (.of B)).hom.hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (b : B))) = _
  rw [Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of B)) (b : B)]
  exact HomogeneousSections.secRingHom_coe D S b _

/-- **The global section of `𝓑ₖ` named by a homogeneous element of degree `k` is in the image of
`ψ` over every open**, by restriction. -/
theorem mem_psiImage_secIncl (V : X.Opens) {k : ℕ} (b : ↥(𝒜 k)) :
    HomogeneousSections.secIncl D S b (op V) ∈ psiImage 𝒜 f D S hsc V := by
  obtain ⟨u, hu⟩ := mem_psiImage_of_le 𝒜 f D S hsc
    (le_top : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))
    (mem_psiImage_secIncl_top 𝒜 f D S hsc b)
  refine ⟨u, hu.trans ?_⟩
  change ConcreteCategory.hom (D.sheaf.right.obj.map (homOfLE _).op)
      (D.alg.ungradedIncl (k : ℤ)
        ((S.sec b).eval (op (f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))))) = _
  refine Eq.trans (D.alg.ungradedIncl_naturality (homOfLE
    (le_top : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))).op (k : ℤ) _) ?_
  exact congrArg (D.alg.ungradedIncl (k : ℤ))
    (PresheafOfModules.sections_property (S.sec b)
      (homOfLE (le_top : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of A)).Opens))).op)

/-- **The generation step, isolated.** The degree-`k` inclusion of *every* section of `𝓑ₖ` over
an affine open lies in the image of `ψ`. This is the only part of the local surjectivity argument
that depends on where the sheaf of graded algebras comes from. -/
def HasAffinePsiGeneration : Prop :=
  ∀ (V : X.Opens), IsAffineOpen V → ∀ (k : ℕ) (x : (D.alg.piece (k : ℤ)).val.obj (op V)),
    D.alg.ungradedIncl (k : ℤ) x ∈ psiImage 𝒜 f D S hsc V

/-- The degree-`n` inclusion of a zero section is in the image of `ψ`. -/
private theorem mem_psiImage_ungradedIncl_of_eq_zero {V : X.Opens} (n : ℤ)
    {x : (D.alg.piece n).val.obj (op V)} (hx : x = 0) :
    D.alg.ungradedIncl n x ∈ psiImage 𝒜 f D S hsc V := by
  subst hx
  exact mem_psiImage_congr 𝒜 f D S hsc
    (Stacks.GradedAlgebra.inclSheaf_zero D.alg.toPresheafGradedAlgebra _ n).symm
    (psiImage 𝒜 f D S hsc V).zero_mem

/-- **The degree-`n` inclusion of a section of `𝓑ₙ` over an affine open is in the image of `ψ`**,
in every integer degree: in a negative degree the homogeneous piece is a zero object. -/
theorem mem_psiImage_ungradedIncl (hgen : HasAffinePsiGeneration 𝒜 f D S hsc)
    {V : X.Opens} (hV : IsAffineOpen V) (n : ℤ)
    (x : (D.alg.piece n).val.obj (op V)) :
    D.alg.ungradedIncl n x ∈ psiImage 𝒜 f D S hsc V := by
  rcases lt_or_ge n 0 with hn | hn
  · have hsub : Subsingleton ↥((D.alg.piece n).val.obj (op V)) :=
      Stacks.subsingleton_of_isZero (D.isZero_of_neg n hn) (op V)
    exact mem_psiImage_ungradedIncl_of_eq_zero 𝒜 f D S hsc n (@Subsingleton.elim _ hsub x 0)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hgen V hV k x

/-- **Every section of the direct sum of the homogeneous sections over an affine open is in the
image of `ψ`**: a section of the presheaf direct sum is a *finite* sum of homogeneous ones
(`Stacks.GradedAlgebra.incl_induction`) and the image is a subring. -/
theorem mem_psiImage_totalUnit (hgen : HasAffinePsiGeneration 𝒜 f D S hsc)
    {V : X.Opens} (hV : IsAffineOpen V)
    (a : D.alg.toPresheafGradedAlgebra.Total (op V)) :
    D.alg.toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (X : TopCat)) (op V) a ∈ psiImage 𝒜 f D S hsc V := by
  induction a using D.alg.toPresheafGradedAlgebra.incl_induction with
  | zero =>
      exact mem_psiImage_congr 𝒜 f D S hsc (map_zero _).symm
        (psiImage 𝒜 f D S hsc V).zero_mem
  | incl n x => exact mem_psiImage_ungradedIncl 𝒜 f D S hsc hgen hV n x
  | add a a' ha ha' =>
      exact mem_psiImage_congr 𝒜 f D S hsc (map_add _ a a').symm
        ((psiImage 𝒜 f D S hsc V).add_mem ha ha')

/-- **`ψ` is surjective on the sections over an affine open.** Over an affine open the sections of
`𝓐` are the direct sum of the sections of the homogeneous pieces
(`Stacks.RelativeSpec.totalSectionsRingEquiv`), and every such section is in the image. -/
theorem surjective_basePullbackHom_app_of_isAffineOpen
    (hgen : HasAffinePsiGeneration 𝒜 f D S hsc) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (ConcreteCategory.hom
      ((HomogeneousSections.basePullbackHom D S f hsc).right.hom.app (op V))) := by
  intro s
  have hmem := mem_psiImage_totalUnit 𝒜 f D S hsc hgen hV
    ((Stacks.RelativeSpec.totalSectionsRingEquiv X D.alg
      (fun i j W a b => D.isCommutative.mul_comm i j W a b) hV).symm s)
  obtain ⟨u, hu⟩ := mem_psiImage_congr 𝒜 f D S hsc
    ((Stacks.RelativeSpec.totalSectionsRingEquiv X D.alg
      (fun i j W a b => D.isCommutative.mul_comm i j W a b) hV).apply_symm_apply s) hmem
  exact ⟨u, hu⟩

/-- **`ψ : f^* 𝔅 ⟶ 𝓐` is locally surjective**, for an arbitrary `f : X ⟶ Spec A` and an arbitrary
sheaf of graded algebras meeting the generation hypothesis: the affine opens below an open
generate a covering sieve of it (`AlgebraicGeometry.generate_affineOpensPresieve_mem`) and `ψ` is
surjective on the sections over each of them. -/
theorem isLocallySurjective_basePullbackHom
    (hgen : HasAffinePsiGeneration 𝒜 f D S hsc) :
    CategoryTheory.Sheaf.IsLocallySurjective
      (HomogeneousSections.basePullbackHom D S f hsc).right := by
  refine ⟨fun {W} s => ?_⟩
  refine (Opens.grothendieckTopology (X : TopCat)).superset_covering
      ((Sieve.generate_le_iff _ _).2 ?_) (generate_affineOpensPresieve_mem X W)
  intro V i hV
  exact surjective_basePullbackHom_app_of_isAffineOpen 𝒜 f D S hsc hgen hV
    (ConcreteCategory.hom (D.sheaf.right.obj.map i.op) s)

end Generic

/-! ### `𝓑 = f^* B̃`: the generation step, and the local surjectivity -/

/-- **`ψ : f^* 𝔅 ⟶ 𝓐` for `𝓑 = f^* B̃`**, with its structure-map compatibility supplied by
`isStructureCompatible_pullbackGradedQcoh`. -/
abbrev pullbackBaseHom :
    (algebraPullback f).obj (pushforwardAlgebra (algebraSpecToBase A B)) ⟶
      (pullbackGradedQcoh 𝒜 f).sheaf :=
  HomogeneousSections.basePullbackHom (pullbackGradedQcoh 𝒜 f)
    (pullbackHomogeneousSections 𝒜 f) f (isStructureCompatible_pullbackGradedQcoh 𝒜 f)

/-- The image of `ψ` for `𝓑 = f^* B̃`, abbreviated. -/
abbrev pullbackPsiImage (V : X.Opens) :
    Subring ↥(AlgebraSheaf.sections (pullbackGradedQcoh 𝒜 f).sheaf V) :=
  psiImage 𝒜 f (pullbackGradedQcoh 𝒜 f) (pullbackHomogeneousSections 𝒜 f)
    (isStructureCompatible_pullbackGradedQcoh 𝒜 f) V

/-- **The degree-`k` inclusion of a section of `𝓑ₖ` over an affine open is in the image of `ψ`.**
This is the generation step for `𝓑 = f^* B̃`: the sections of `𝓑ₖ = f^*(B̃ₖ)` over an affine `V`
are the base change along `f.appLE ⊤ V` of the global sections of `B̃ₖ`, every global section of
`B̃ₖ` is named by a homogeneous element, and the image of `ψ` is a `Γ(X, V)`-submodule containing
the sections those elements name. -/
theorem mem_psiImage_ungradedIncl_natDegree {V : X.Opens} (hV : IsAffineOpen V) (k : ℕ)
    (x : ((pullbackGradedAlg 𝒜 f).piece (k : ℤ)).val.obj (op V)) :
    (pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ) x ∈ pullbackPsiImage 𝒜 f V := by
  -- the pullbacks of global sections of `B̃ₖ` are in the image
  have hgen : ∀ a : ((specGradedAlg 𝒜).piece (k : ℤ)).val.obj (op (⊤ : (Spec (.of A)).Opens)),
      (pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)
        (Scheme.Modules.pullbackSection f ((specGradedAlg 𝒜).piece (k : ℤ)) ⊤ V le_top a) ∈
        pullbackPsiImage 𝒜 f V := by
    intro a
    obtain ⟨b, hb⟩ := exists_specSection_eval_top 𝒜 k a
    refine mem_psiImage_congr 𝒜 f _ _ _ ?_
      (mem_psiImage_secIncl 𝒜 f (pullbackGradedQcoh 𝒜 f) (pullbackHomogeneousSections 𝒜 f)
        (isStructureCompatible_pullbackGradedQcoh 𝒜 f) V b)
    change (pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)
        (((pullbackHomogeneousSections 𝒜 f).sec b).eval (op V)) = _
    refine congrArg ((pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)) ?_
    refine Eq.trans (pullbackSections_eval f ((specGradedAlg 𝒜).piece (k : ℤ))
      (specSection 𝒜 b) (op V)) ?_
    exact congrArg
      (Scheme.Modules.pullbackSection f ((specGradedAlg 𝒜).piece (k : ℤ)) ⊤ V le_top) hb
  -- every section over `V` comes from the base change
  obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso
    (affinePullbackSectionsBaseChangeIso f ((specGradedAlg 𝒜).piece (k : ℤ))
      (isAffineOpen_top (Spec (.of A))) hV le_top).hom).2 x
  subst ht
  refine ModuleCat.ExtendScalars.forall_of_one_tmul
    (f.appLE (⊤ : (Spec (.of A)).Opens) V le_top).hom
    (fun z => (pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)
      ((affinePullbackSectionsBaseChangeIso f ((specGradedAlg 𝒜).piece (k : ℤ))
        (isAffineOpen_top (Spec (.of A))) hV le_top).hom z) ∈ pullbackPsiImage 𝒜 f V)
    ?_ ?_ ?_ t
  · intro z z' hz hz'
    refine mem_psiImage_congr 𝒜 f _ _ _ ?_ ((pullbackPsiImage 𝒜 f V).add_mem hz hz')
    refine Eq.trans
      ((pullbackGradedAlg 𝒜 f).ungradedIncl_add (k : ℤ) (op V) _ _).symm ?_
    exact congrArg ((pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)) (map_add _ z z').symm
  · intro c z hz
    refine mem_psiImage_congr 𝒜 f _ _ _ ?_
      ((pullbackPsiImage 𝒜 f V).mul_mem
        (mem_psiImage_structureMap 𝒜 f (pullbackGradedQcoh 𝒜 f)
          (pullbackHomogeneousSections 𝒜 f)
          (isStructureCompatible_pullbackGradedQcoh 𝒜 f) V c) hz)
    refine Eq.trans
      ((pullbackGradedAlg 𝒜 f).ungradedIncl_smul (k : ℤ) (op V) c _).symm ?_
    refine congrArg ((pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ)) ?_
    exact ((affinePullbackSectionsBaseChangeIso f ((specGradedAlg 𝒜).piece (k : ℤ))
      (isAffineOpen_top (Spec (.of A))) hV le_top).hom.hom.map_smul c z).symm
  · intro m
    refine mem_psiImage_congr 𝒜 f _ _ _ ?_ (hgen m)
    exact congrArg ((pullbackGradedAlg 𝒜 f).ungradedIncl (k : ℤ))
      (affinePullbackSectionsBaseChangeIso_one_tmul f ((specGradedAlg 𝒜).piece (k : ℤ))
        (isAffineOpen_top (Spec (.of A))) hV le_top m).symm

/-- The generation hypothesis holds for `𝓑 = f^* B̃`. -/
theorem hasAffinePsiGeneration_pullback :
    HasAffinePsiGeneration 𝒜 f (pullbackGradedQcoh 𝒜 f) (pullbackHomogeneousSections 𝒜 f)
      (isStructureCompatible_pullbackGradedQcoh 𝒜 f) :=
  fun _V hV k x => mem_psiImage_ungradedIncl_natDegree 𝒜 f hV k x

/-- **`ψ` is locally surjective for `𝓑 = f^* B̃`.** -/
theorem isLocallySurjective_pullbackBaseHom :
    CategoryTheory.Sheaf.IsLocallySurjective (pullbackBaseHom 𝒜 f).right :=
  isLocallySurjective_basePullbackHom 𝒜 f (pullbackGradedQcoh 𝒜 f)
    (pullbackHomogeneousSections 𝒜 f) (isStructureCompatible_pullbackGradedQcoh 𝒜 f)
    (hasAffinePsiGeneration_pullback 𝒜 f)

/-! ### The proper structure morphism of the base change -/

/-- **`f' : X' ⟶ Spec B`, the structure morphism of [Stacks, Tag 0897]'s base change**, for
`𝓑 = f^* B̃`. -/
def pullbackStructureHom : (pullbackGradedQcoh 𝒜 f).relSpec.left ⟶ Spec (.of B) :=
  HomogeneousSections.structureHom (pullbackGradedQcoh 𝒜 f) (pullbackHomogeneousSections 𝒜 f) f
    (isStructureCompatible_pullbackGradedQcoh 𝒜 f)

/-- **`f' : X' ⟶ Spec B` is proper**, with nothing assumed beyond [Stacks, Tag 0897]'s own
hypothesis that `f : X ⟶ Spec A` is proper: `X' = Spec_X(f^* B̃)` is a closed subscheme of the
honest base change `Spec(B) ×_{Spec A} X` because `ψ` is locally surjective, and a closed
subscheme of a base change along a proper morphism is proper over the new base
([Stacks, Tag 01W4]). -/
theorem isProper_pullbackStructureHom (hf : _root_.AlgebraicGeometry.IsProper f) :
    _root_.AlgebraicGeometry.IsProper (pullbackStructureHom 𝒜 f) :=
  HomogeneousSections.isProper_structureHom (pullbackGradedQcoh 𝒜 f)
    (pullbackHomogeneousSections 𝒜 f) f (isStructureCompatible_pullbackGradedQcoh 𝒜 f)
    (isLocallySurjective_pullbackBaseHom 𝒜 f) hf

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
