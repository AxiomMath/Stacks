module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSpec

/-!
# The quotient morphism `Y ⟶ X'` of Stacks 0AGG is proper and surjective

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian,
and let `π : Y ⟶ X' = \underline{Spec}_X(𝒜)` be the morphism to the relative spectrum of the
equalizer `𝒜` of `s♯, t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R`
(`AlgebraicGeometry.Space.kernelPairSpecπ`). The proof of Stacks 0AGG needs `π` to be proper and
surjective *before* it knows that `X'` is the coequalizer of `s, t`, because it applies Stacks
0GG0 to `π`. This file proves both.

Properness is clauses (1) and (2) of the source: `X' ⟶ X` is finite, hence separated, so `π` is
proper by Stacks 04NX. For surjectivity the source uses the Stein factorization; here, as in
`AlgebraicGeometry.Space.KernelPairCoequalizer.isSurjective_π_of_isProper`, `π` is shown to be
scheme-theoretically dominant, so that the image of `|π|` is dense, and it is closed because `π`
is universally closed. Scheme-theoretic dominance comes from the mapping property of the relative
spectrum: the scheme-theoretic image `W ⊆ X'` of `π` is affine over `X`, the direct image of
`𝒪_W` maps to `g_* 𝒪_Y` through a map equalized by `s♯` and `t♯`, hence through `𝒜`, and the
resulting morphism `X' ⟶ W` over `X` splits the inclusion of `W`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.equalizerAlgebraLift`: the mapping property of the
  equalizer of two morphisms of algebra sheaves.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_kernelPairSpecπ_eq_top`: `π` is
  scheme-theoretically dominant.
* `AlgebraicGeometry.Space.isProper_kernelPairSpecπ` and
  `AlgebraicGeometry.Space.isSurjective_kernelPairSpecπ`: `π` is proper and surjective.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {A C A' : AlgebraSheaf.{u, u} B S hS F hF} (φ ψ : A ⟶ C)

/-- **The mapping property of the equalizer of two morphisms of algebra sheaves**: a morphism
`χ : A' ⟶ A` equalizing `φ` and `ψ` factors through the equalizer. -/
def equalizerAlgebraLift (χ : A' ⟶ A) (h : χ ≫ φ = χ ≫ ψ) : A' ⟶ equalizerAlgebra φ ψ where
  right := ⟨{ app := fun U => CommRingCat.ofHom ((χ.right.hom.app U).hom.codRestrict
                (equalizerSections φ ψ U) fun a =>
                  congrArg (fun k : A' ⟶ C => (k.right.hom.app U).hom a) h)
              naturality := fun U V i => by
                ext a
                exact Subtype.ext (app_map χ i a) }⟩
  comm U r := Subtype.ext (χ.comm U r)

/-- The lift `equalizerAlgebraLift φ ψ χ h` composed with the inclusion of the equalizer is `χ`. -/
@[reassoc (attr := simp)]
theorem equalizerAlgebraLift_ι (χ : A' ⟶ A) (h : χ ≫ φ = χ ≫ ψ) :
    equalizerAlgebraLift φ ψ χ h ≫ equalizerι φ ψ = χ :=
  Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl)))

/-- Two morphisms into the equalizer agreeing after the inclusion are equal. -/
theorem equalizerι_hom_ext {a b : A' ⟶ equalizerAlgebra φ ψ}
    (h : a ≫ equalizerι φ ψ = b ≫ equalizerι φ ψ) : a = b := by
  refine Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
  ext x
  exact Subtype.ext (congrArg (fun k : A' ⟶ A => (k.right.hom.app U).hom x) h)

end AlgebraSheaf

section KernelPairSpec

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X}

/-- **The quotient morphism `π : Y ⟶ X'` is scheme-theoretically dominant.** The
scheme-theoretic image `W` of `π` is affine over `X`, and the morphism `Y ⟶ W` induces a map
of `𝒪_X`-algebras `𝒪_W ⟶ g_* 𝒪_Y` equalized by `s♯` and `t♯`; it factors through `𝒜`, and
the resulting morphism `X' ⟶ W` over `X` splits the inclusion of `W`. -/
theorem schemeTheoreticImageSubfunctor_kernelPairSpecπ_eq_top (hg : IsProper B S hS g.hom) :
    schemeTheoreticImageSubfunctor B S hS (kernelPairSpecπ hg).hom = ⊤ := by
  let X'o := kernelPairSpec hg
  let W := schemeTheoreticImageSubfunctor B S hS (kernelPairSpecπ hg).hom
  have hle := range_le_schemeTheoreticImageSubfunctor B S hS (kernelPairSpecπ hg).hom
  have hW := isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (kernelPairSpecπ hg).hom
    X'o.obj.left.property
  let Wsp : AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
  let ιW : Wsp ⟶ X'o.obj.left := ObjectProperty.homMk W.ι
  let ℓ : Y ⟶ Wsp := ObjectProperty.homMk (Subfunctor.lift (G := W) (kernelPairSpecπ hg).hom hle)
  have hℓ : ℓ ≫ ιW = kernelPairSpecπ hg :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι (kernelPairSpecπ hg).hom hle)
  have hmono : ∀ {A : AlgebraicSpaces B S hS} (a b : A ⟶ Wsp), a ≫ ιW = b ≫ ιW → a = b :=
    fun a b h => ObjectProperty.hom_ext _ ((cancel_mono W.ι).1 (congrArg (·.hom) h))
  let Wo : AffineOver B S hS X :=
    ⟨Over.mk (ιW ≫ X'o.obj.hom), isAffineHom_comp B S hS W.ι X'o.obj.hom.hom
      (isAffineHom_of_isClosedImmersion B S hS W.ι hW.2) X'o.property⟩
  let ℓo : Over.mk g ⟶ Wo.obj := Over.homMk ℓ ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ X'o.obj.hom) hℓ).trans (kernelPairSpecπ_comp_toTarget hg)))
  let ιWo : Wo.obj ⟶ X'o.obj := Over.homMk ιW rfl
  have hℓι : ℓo ≫ ιWo = kernelPairSpecπOver hg := Over.OverMorphism.ext hℓ
  have heq : kernelPairFstOver g ≫ ℓo = kernelPairSndOver g ≫ ℓo :=
    Over.OverMorphism.ext (hmono _ _ (by
      show (pullback.fst g g ≫ ℓ) ≫ ιW = (pullback.snd g g ≫ ℓ) ≫ ιW
      rw [Category.assoc, Category.assoc, hℓ]
      exact kernelPairSpecπ_equalizes hg))
  have hsharp : pushforwardAlgebraMap B S hS ℓo ≫ kernelPairFstMap g =
      pushforwardAlgebraMap B S hS ℓo ≫ kernelPairSndMap g := by
    rw [kernelPairFstMap_def, kernelPairSndMap_def, ← pushforwardAlgebraMap_comp,
      ← pushforwardAlgebraMap_comp, heq]
  let ρ : pushforwardAlgebra B S hS Wo.obj ⟶ pushforwardAlgebra B S hS X'o.obj :=
    AlgebraSheaf.equalizerAlgebraLift _ _ _ hsharp ≫ (kernelPairSpecIso hg).inv
  let r : X'o.obj ⟶ Wo.obj := (overHomEquivPushforwardAlgebraHom B S hS X'o.obj Wo).symm ρ
  have hr : pushforwardAlgebraMap B S hS r = ρ :=
    (overHomEquivPushforwardAlgebraHom B S hS X'o.obj Wo).apply_symm_apply ρ
  have hrι : r ≫ ιWo = 𝟙 _ := by
    refine eq_of_pushforwardAlgebraMap_eq B S hS X'o ?_
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id, hr]
    show pushforwardAlgebraMap B S hS ιWo ≫ AlgebraSheaf.equalizerAlgebraLift _ _ _ hsharp ≫
      (kernelPairSpecIso hg).inv = _
    have key : pushforwardAlgebraMap B S hS ιWo ≫
        AlgebraSheaf.equalizerAlgebraLift _ _ _ hsharp = (kernelPairSpecIso hg).hom :=
      AlgebraSheaf.equalizerι_hom_ext (kernelPairFstMap g) (kernelPairSndMap g) (by
        rw [Category.assoc, AlgebraSheaf.equalizerAlgebraLift_ι, ← pushforwardAlgebraMap_comp,
          hℓι, pushforwardAlgebraMap_kernelPairSpecπOver]
        rfl)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (kernelPairSpecIso hg).inv) key).trans
      (kernelPairSpecIso hg).hom_inv_id)
  have hrι' : r.left.hom ≫ W.ι = 𝟙 _ := congrArg (fun k => k.left.hom) hrι
  exact (Subfunctor.eq_top_iff_isIso W).2 ⟨⟨r.left.hom, (cancel_mono W.ι).1 (by
    rw [Category.assoc, hrι', Category.comp_id, Category.id_comp]), hrι'⟩⟩

/-- **The quotient morphism `π : Y ⟶ X'` is proper** (clause (2) of Stacks 0AGG): `g = π ≫ ν`
is proper and `ν : X' ⟶ X` is finite, hence separated, so `π` is proper by Stacks 04NX. -/
theorem isProper_kernelPairSpecπ (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsProper B S hS (kernelPairSpecπ hg).hom :=
  isProper_of_comp_of_isSeparated B S hS Y.property (kernelPairSpec hg).obj.left.property
    X.property _ _
    (by
      have h := congrArg (fun k => k.hom) (kernelPairSpecπ_comp_toTarget hg)
      change (kernelPairSpecπ hg).hom ≫ (kernelPairSpecToTarget hg).hom = g.hom at h
      rw [h]
      exact hg)
    (isSeparated_of_isFinite B S hS _ (kernelPairSpec hg).obj.left.property X.property
      (isFinite_kernelPairSpecToTarget hg hX))

/-- **The quotient morphism `π : Y ⟶ X'` is surjective** (clause (3) of Stacks 0AGG, proved
before the coequalizer property): it is scheme-theoretically dominant, so the image of `|π|` is
dense (Stacks 082Z, `π` being quasi-compact), and closed because `π` is universally closed. -/
theorem isSurjective_kernelPairSpecπ (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsSurjective B S hS (kernelPairSpecπ hg).hom := by
  have hπ := isProper_kernelPairSpecπ hg hX
  have hqc : IsQuasiCompact B S hS (kernelPairSpecπ hg).hom :=
    isQuasiCompact_of_universallyClosed B S hS Y.property (kernelPairSpec hg).obj.left.property
      _ hπ.2.2
  have hiso : IsIso (schemeTheoreticImageSubfunctor B S hS (kernelPairSpecπ hg).hom).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (schemeTheoreticImageSubfunctor_kernelPairSpecπ_eq_top hg)
  have hdense : closure (Set.range (pointsMap B S hS Y.obj (kernelPairSpecπ hg).hom)) =
      Set.univ := by
    rw [← range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS _
      Y.property (kernelPairSpec hg).obj.left.property hqc]
    exact Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS _)
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS Y.obj (kernelPairSpecπ hg).hom)) :=
    (isClosed_of_universallyClosed B S hS (kernelPairSpec hg).obj.left.property _
      hπ.2.2).isClosed_range
  exact Set.range_eq_univ.1 (by rw [← hclosed.closure_eq, hdense])

end KernelPairSpec

end AlgebraicGeometry.Space

end
