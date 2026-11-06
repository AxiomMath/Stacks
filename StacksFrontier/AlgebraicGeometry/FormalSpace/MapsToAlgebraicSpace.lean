module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.LocalRing.NonLocalRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AdicCompleteMonoSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.RingTheory.CompleteLocalRing.FiniteEtaleResidueExtension
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteEtale
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Maps from an affine formal spectrum to an algebraic space (Stacks 0AQH)

Let `S` be a scheme, `R` a Noetherian complete local `S`-algebra and `X` an algebraic space
over `S`.
**Stacks 0AQH** says that the restriction map

`Mor_S(Spec R, X) ⟶ Mor_S(Spf R, X)`

is bijective. This file proves both halves.

## Main definitions

* `AlgebraicGeometry.FormalSpace.upliftedSheaf`: an algebraic space regarded as a sheaf of
  sets in the universe in which the formal spectrum is built.

## Main results

* `AlgebraicGeometry.FormalSpace.eq_of_forall_quotientPow_factorization`: two points of an
  algebraic space over `Spec R`, for `R` complete for a maximal ideal `I`, which agree
  after restriction along a factorization of every truncation `Spec (R / Iⁿ) ⟶ Spec R`,
  are equal.
* `AlgebraicGeometry.FormalSpace.injective_map_into_algebraicSpace` and
  `AlgebraicGeometry.FormalSpace.surjective_map_into_algebraicSpace`: the two halves of
  **Stacks 0AQH**, assembled into
  `AlgebraicGeometry.FormalSpace.bijective_map_into_algebraicSpace`.

## Implementation notes

*Injectivity.* Write `T` for the fibre product `Spec R ×_{(x, y), X ×_S X, Δ} X` of the two
points. Because the diagonal of an algebraic space is representable, `T` is an object of the
site, and because the diagonal is a monomorphism — **Stacks 02X4 part (2)**, that is
`AlgebraicGeometry.presheaf_monomorphisms_diag`, which is part (3) of **Stacks 03HK** — the
projection `g : T ⟶ Spec R` is a monomorphism of schemes. A point of `T` over a scheme `Z`
is exactly a map `Z ⟶ Spec R` equalizing `x` and `y`, so the hypothesis supplies a section
of `g` over every truncation `Spec (R / Iⁿ)`, and
`AlgebraicGeometry.exists_section_of_mono_of_forall_section_quotient_pow` assembles those
into a section over `Spec R`. A section of `g` makes the pair `(x, y)` factor through the
diagonal, which is `x = y`.

*What injectivity does not need.* The Stacks proof of that half runs through the local
ring `𝒪_{T,t}` and therefore cites **Stacks 01T6** (local Noetherianness of `T`) and
**Stacks 00IP** (Krull intersection), and needs parts (2), (4) and (5) of 03HK to know that
`T → Spec R` is locally of finite type. None of that is used here; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.MoreMorphisms.AdicCompleteMonoSection`. In
particular no Noetherian hypothesis on `R` appears there, where the source assumes one.

*Surjectivity.* An étale chart `U ⟶ X` is pulled back along the residue field point; the
resulting nonempty disjoint union of spectra of finite separable extensions of `k = R / 𝔪`
supplies a finite separable `k'/k` (**Stacks 02GL**) together with a point of the chart over
it. The finite étale extension `R ⊆ R'` of Noetherian complete local rings realising `k'/k`
(**Stacks 04GK**, **04GM**) is
`exists_finite_etale_isNoetherianCompleteLocalRing_residueField`. The truncated points lift
into the chart along the tower of square-zero thickenings of quotient stages
(`isSquareZeroClosedImmersion_adicTowerMap`,
`exists_compatible_lifts_adicTower_of_formallyEtale`), and
`AlgebraicGeometry.FormalSpace.isWeaklyAdmissible_maximalAdicTopology` makes the `𝔪`-adic
topology of a Noetherian complete local ring weakly admissible, instantiating
**Stacks 0AQG** for `R'`; that produces a morphism `Spec R' ⟶ X`. Descent along the flat
morphism of finite presentation `Spec R' ⟶ Spec R`,
`bijective_mapToEqualizer_of_isSheaf_of_flat`, then produces the morphism out of `Spec R`.
Its cocycle condition comes from the injectivity half applied to the factors of
`R' ⊗_R R'`, a finite product of Noetherian complete local rings by **Stacks 0325** part (2),
`finite_isProduct_isNoetherianCompleteLocalRing`.

Worth recording about that route: the lifting step is cited in the source as
**Stacks 0616**, which the library carries for algebraic spaces as
`AlgebraicGeometry.Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale`; but the
morphism actually lifted along is the represented base change `Spec (R'/𝔪ⁿR') ×_X U`, which is
a *scheme*, so only the scheme-level "étale implies formally étale" is needed, and that is
`AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale`.

## References

* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_presheaf_MapsToAlgebraicSpace
    {J : Type*} [Category* J] [HasLimitsOfShape J (Type u)] :
    HasLimitsOfShape J ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_MapsToAlgebraicSpace :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_MapsToAlgebraicSpace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An algebraic space over `S`, regarded as a sheaf of sets one universe up. The formal
spectrum is built as a colimit in that universe, so this is the target in which maps out of
a formal spectrum are compared with maps out of an ordinary spectrum. -/
public def upliftedSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ⟨X ⋙ uliftFunctor.{u + 1},
    (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS)
      (X ⋙ uliftFunctor.{u + 1})).2
        (Presieve.isSheaf_comp_uliftFunctor (BigFppfOver.topology B S hS)
          ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) X).1 hX.isSheaf))⟩

/-- The sections of `AlgebraicGeometry.FormalSpace.upliftedSheaf` are the sections of the
algebraic space, lifted. -/
public theorem upliftedSheaf_obj_obj (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (Z : (BigFppfOver B S hS)ᵒᵖ) :
    (upliftedSheaf X hX).obj.obj Z = ULift.{u + 1} (X.obj Z) := rfl

/-- Composing with a factorisation, read in schemes. Stated separately because at the point
of use the target of the projection is spelled as the spectrum of a ring rather than as the
underlying scheme of a site object, and the two spellings are only definitionally equal. -/
private theorem comp_map_toScheme_of_comp_eq {Z T W : BigFppfOver B S hS}
    {τ : Z ⟶ T} {q : T ⟶ W} {ζ : Z ⟶ W} (hτ : τ ≫ q = ζ) {V : Scheme.{u}}
    (c : V ⟶ (BigFppfOver.toScheme B S hS).obj Z) :
    (c ≫ (BigFppfOver.toScheme B S hS).map τ) ≫ (BigFppfOver.toScheme B S hS).map q =
      c ≫ (BigFppfOver.toScheme B S hS).map ζ := by
  rw [Category.assoc, ← Functor.map_comp, hτ]

/-- Transport an equality of postcompositions along a factorisation `u ≫ v = w`. Stated
separately because at the point of use the colimit presenting the formal spectrum carries
two definitionally equal spellings, which a rewrite cannot see through. -/
private theorem eq_comp_of_eq_comp_of_comp_eq {C : Type*} [Category C] {A A' A'' A''' : C}
    (u : A ⟶ A') (v : A' ⟶ A'') {w : A ⟶ A''} (hw : u ≫ v = w) {f₁ f₂ : A'' ⟶ A'''}
    (h : v ≫ f₁ = v ≫ f₂) : w ≫ f₁ = w ≫ f₂ := by
  rw [← hw, Category.assoc, Category.assoc, h]

/-- A section of the underlying scheme morphism of a morphism of the site is a section in
the site: it is a morphism of the size-bounded subcategory because that inclusion is full,
and it lies over the base because the morphism it sections does. -/
private theorem exists_siteHom_section {T W : BigFppfOver B S hS} (q : T ⟶ W)
    (σ : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hσ : σ ≫ (BigFppfOver.toScheme B S hS).map q = 𝟙 _) :
    ∃ τ : W ⟶ T, τ ≫ q = 𝟙 W := by
  obtain ⟨σ₀, hmap⟩ : ∃ r : W.left ⟶ T.left, B.inclusion.map r = σ :=
    ⟨B.inclusion.preimage σ, B.inclusion.map_preimage σ⟩
  have h₁ : σ₀ ≫ q.left = 𝟙 W.left := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, hmap, B.inclusion.map_id]
  exact ⟨Over.homMk σ₀ (by rw [← Over.w q, ← Category.assoc, h₁, Category.id_comp]),
    Over.OverMorphism.ext h₁⟩

/-- A morphism of the site whose underlying morphism of schemes is an isomorphism is one. -/
private theorem isIso_of_isIso_inclusion_map_left {U V : BigFppfOver B S hS} (v : U ⟶ V)
    [IsIso (B.inclusion.map v.left)] : IsIso v := by
  have : IsIso v.left := isIso_of_reflects_iso v.left B.inclusion
  let : IsIso ((Over.forget _).map v) := inferInstanceAs (IsIso v.left)
  exact isIso_of_reflects_iso v (Over.forget _)

/-- If two morphisms into an algebraic space agree after precomposition with the maps induced by
`i₁` and `i₂`, then their sections agree after restriction along `i₁` and `i₂`. -/
private theorem map_section_eq_of_comp_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {T₁ T₂ V : BigFppfOver B S hS} (i₁ : V ⟶ T₁) (i₂ : V ⟶ T₂)
    {f₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T₁ ⟶ upliftedSheaf X hX}
    {f₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T₂ ⟶ upliftedSheaf X hX}
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i₁ ≫ f₁ =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i₂ ≫ f₂) :
    X.map i₁.op (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) f₁ :
        ULift (X.obj (op T₁))).down =
      X.map i₂.op (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) f₂ :
        ULift (X.obj (op T₂))).down :=
  (congrArg ULift.down (Sheaf.sectionEquiv_map_comp _ i₁ f₁)).symm.trans
    ((congrArg (fun f => (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) f :
        ULift (X.obj (op V))).down) h).trans
      (congrArg ULift.down (Sheaf.sectionEquiv_map_comp _ i₂ f₂)))

/-- If `r ≫ diag X = π ≫ prod.lift α β`, then `π` equalizes `α` and `β`. -/
private theorem comp_eq_comp_of_comp_diag_eq_lift {C : Type*} [Category C] [HasBinaryProducts C]
    {W Y X : C} (r : W ⟶ X) (π : W ⟶ Y) (α β : Y ⟶ X)
    (h : r ≫ diag X = π ≫ prod.lift α β) : π ≫ α = π ≫ β := by
  have h₁ := congrArg (· ≫ prod.fst) h
  have h₂ := congrArg (· ≫ prod.snd) h
  simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.symm.trans h₂

/-- **The injectivity half of Stacks 0AQH.** Let `R` be a ring complete for a maximal ideal
`I`, with `Spec R` an object of the site over `S`, and let `X` be an algebraic space over
`S`. Two `R`-points `x`, `y` of `X` are equal as soon as, for every `n`, the truncation
`Spec (R / Iⁿ) ⟶ Spec R` factors through some object `Z` of the site over `Spec R` on which
`x` and `y` already agree.

No Noetherian hypothesis is needed, and only the monomorphism part of the diagonal of `X`
is used. -/
public theorem eq_of_forall_quotientPow_factorization
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I.IsMaximal) [IsAdicComplete I R]
    {hRS : B.Contains (Spec (.of R))} {p : Spec (.of R) ⟶ S}
    {x y : X.obj (op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)))}
    (h : ∀ n : ℕ, ∃ (Z : BigFppfOver B S hS)
          (ζ : Z ⟶ (BigAffineFppf.inclusion B S hS).obj (specOver hRS p))
          (c : Spec (.of (R ⧸ I ^ n)) ⟶ (BigFppfOver.toScheme B S hS).obj Z),
        c ≫ (BigFppfOver.toScheme B S hS).map ζ =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ∧
          X.map ζ.op x = X.map ζ.op y) :
    x = y := by
  classical
  -- the fibre product of the two points along the diagonal, and its mono projection
  have hdiag := presheaf_monomorphisms_diag B S hS X hX
  have hrep : yoneda.relativelyRepresentable (diag X) := hdiag.rep
  set α : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ X :=
    yonedaEquiv.symm x with hα
  set β : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ X :=
    yonedaEquiv.symm y with hβ
  set g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ X ⨯ X :=
    prod.lift α β with hg
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
    hdiag.property_snd g
  -- every truncation admits a section of the projection
  have hsec : ∀ n : ℕ, ∃ s : Spec (.of (R ⧸ I ^ n)) ⟶
      (BigFppfOver.toScheme B S hS).obj (hrep.pullback g),
      s ≫ (BigFppfOver.toScheme B S hS).map (hrep.snd g) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) := by
    intro n
    obtain ⟨Z, ζ, c, hc, hxy⟩ := h n
    have hab : yoneda.map ζ ≫ α = yoneda.map ζ ≫ β := by
      rw [hα, hβ, yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, hxy]
    have hi : (yoneda.map ζ ≫ α) ≫ diag X = yoneda.map ζ ≫ g := by
      refine prod.hom_ext ?_ ?_
      · simp [hg]
      · simp [hg, ← hab]
    exact ⟨c ≫ (BigFppfOver.toScheme B S hS).map (hrep.lift (yoneda.map ζ ≫ α) ζ hi),
      (comp_map_toScheme_of_comp_eq (hrep.lift_snd _ _ _) c).trans hc⟩
  choose s hs using hsec
  obtain ⟨σ, hσ⟩ := @exists_section_of_mono_of_forall_section_quotient_pow R _ I hI _ _
    ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) hmono s hs
  -- read the section back as a morphism of the site
  obtain ⟨τ, hτ⟩ := exists_siteHom_section (hrep.snd g) σ hσ
  -- a section makes the pair of points factor through the diagonal
  have hfac : (yoneda.map τ ≫ hrep.fst g) ≫ diag X = g := by
    rw [Category.assoc, (hrep.isPullback g).w, ← Category.assoc, ← yoneda.map_comp, hτ,
      yoneda.map_id, Category.id_comp]
  have hαβ : α = β := by
    simpa using comp_eq_comp_of_comp_diag_eq_lift _ (𝟙 _) α β (by rwa [Category.id_comp])
  exact yonedaEquiv.symm.injective (by rw [← hα, ← hβ]; exact hαβ)

/-- **The injectivity half of Stacks 0AQH**, in the shape of the bijectivity statement:
restriction along the canonical map `Spf R ⟶ Spec R` is injective on morphisms to an
algebraic space over `S`.

Only the second cofinality condition on the weak ideals of definition is used — that every
power of the maximal ideal contains one — and the Noetherian hypothesis on `R` enters only
through locality and completeness. -/
@[stacks 0AQH "injectivity", sga "3 XV 1.4" "injectivity of (*)", sga "3 XI 3.3" "injectivity"]
public theorem injective_map_into_algebraicSpace
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Injective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec D hRS p hp ≫ f) := by
  classical
  have : IsLocalRing R := hR.isLocal
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hR.isComplete
  intro f₁ f₂ hf
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  refine congrArg ULift.up ?_
  refine eq_of_forall_quotientPow_factorization hX
    (IsLocalRing.maximalIdeal.isMaximal R) (fun n => ?_)
  obtain ⟨J, hJ⟩ := hD n
  refine ⟨(BigAffineFppf.inclusion B S hS).obj (D.stage J),
    (BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS p J (hp J)),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)), ?_, ?_⟩
  · have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
    exact key
  · exact map_section_eq_of_comp_eq _ _ (eq_comp_of_eq_comp_of_comp_eq
      (formalSpectrumInclusion D (OrderDual.toDual J))
      (formalSpectrumToSpec D hRS p hp) (formalSpectrumToSpec_spec D hRS p hp J) hf)

/-! ### The surjectivity half -/

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma formalSpectrum_hom_ext
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (D : QuotientSystem B S hS R)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {f g : formalSpectrum D ⟶ Y}
    (h : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      formalSpectrumInclusion D (OrderDual.toDual J) ≫ f =
        formalSpectrumInclusion D (OrderDual.toDual J) ≫ g) :
    f = g :=
  CategoryTheory.Limits.colimit.hom_ext fun J => h (OrderDual.ofDual J)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The intersection of two weak ideals of definition is a weak ideal of definition. -/
lemma weakIdeal_inf
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    TopologicalRing.IsWeakIdealOfDefinition (I ⊓ J) := by
  refine ⟨hI.1.inter hJ.1, ?_⟩
  intro x hx
  exact hI.2 x hx.1
private lemma diagonalPullback_isRepresentable
    {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S}
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS)
    (x y : X.obj (Opposite.op U)) :
    (pullback (yonedaEquiv.symm
      (yonedaEquiv (Limits.prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))))
      (Limits.diag X)).IsRepresentable :=
  (yoneda_relativelyRepresentable_iff_pullback_representable
    (Limits.diag X)).mp hX.diagonal_representable U
    (yonedaEquiv (Limits.prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma etale_atlas_formallyEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ X)
    (hf : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f) :
    Space.FormallyEtale f := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u}) := ⟨by
    intro V W Z f g hf hg
    let := hf
    let := hg
    infer_instance⟩
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hspaceEtale : Space.IsEtale B S hS f := by
    intro V φ hφ
    exact MorphismProperty.comp_mem _ _ _ hφ hf
  exact (Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale
    B S hS (isAlgebraicSpace_yoneda B S hS U) hX f).mp hspaceEtale |>.2

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Formal étaleness lifts a compatible sequence of sections across a sequence
of square-zero thickenings, once a lift is fixed at the initial stage. -/
private lemma exists_compatible_formallyEtale_lifts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : Space.FormallyEtale a)
    (T : ℕ → BigFppfOver B S hS)
    (i : ∀ n, T n ⟶ T (n + 1))
    (hAff : ∀ n,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (T n)) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (T (n + 1))))
    (hSq : ∀ n, Space.IsSquareZeroClosedImmersion B S hS (i n))
    (x : ∀ n, G.obj (Opposite.op (T n)))
    (hx : ∀ n, G.map (Opposite.op (i n)) (x (n + 1)) = x n)
    (z₀ : F.obj (Opposite.op (T 0)))
    (hz₀ : a.app (Opposite.op (T 0)) z₀ = x 0) :
    ∃ z : ∀ n, F.obj (Opposite.op (T n)),
      z 0 = z₀ ∧
        (∀ n, F.map (Opposite.op (i n)) (z (n + 1)) = z n) ∧
        (∀ n, a.app (Opposite.op (T n)) (z n) = x n) := by
  classical
  let liftNext (n : ℕ)
      (prev : {z : F.obj (Opposite.op (T n)) // a.app (Opposite.op (T n)) z = x n}) :
      {z : F.obj (Opposite.op (T (n + 1))) //
        a.app (Opposite.op (T (n + 1))) z = x (n + 1)} := by
    have hbase : a.app (Opposite.op (T n)) prev.1 =
        G.map (Opposite.op (i n)) (x (n + 1)) := by
      rw [prev.2, ← hx n]
    let h := ha (T n) (T (n + 1)) (hAff n).1 (hAff n).2
      (i n) (hSq n) prev.1 (x (n + 1)) hbase
    exact ⟨Classical.choose h.exists,
      (Classical.choose_spec h.exists).2⟩
  let liftData : ∀ n,
      {z : F.obj (Opposite.op (T n)) // a.app (Opposite.op (T n)) z = x n} :=
    Nat.rec ⟨z₀, hz₀⟩ (fun n prev => liftNext n prev)
  refine ⟨fun n => (liftData n).1, ?_, ?_, ?_⟩
  · rfl
  · intro n
    change F.map (Opposite.op (i n))
      ((liftNext n (liftData n)).1) = (liftData n).1
    have hbase : a.app (Opposite.op (T n)) (liftData n).1 =
        G.map (Opposite.op (i n)) (x (n + 1)) := by
      rw [(liftData n).2, ← hx n]
    exact (Classical.choose_spec (ha (T n) (T (n + 1)) (hAff n).1 (hAff n).2
      (i n) (hSq n) (liftData n).1 (x (n + 1)) hbase).exists).1
  · intro n
    exact (liftData n).2

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exists_finiteEtaleLocalResidueLift
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] :
    ∃ L : IsLocalRing.FiniteIntermediateField.{u, u} (IsLocalRing.ResidueField R) K,
      Nonempty (IsLocalRing.FiniteEtaleLocalResidueLift.{u, u, u} R R K
        (RingEquiv.refl _) L) := by
  let L : IsLocalRing.FiniteIntermediateField.{u, u} (IsLocalRing.ResidueField R) K := ⟨⊤⟩
  exact ⟨L, IsLocalRing.FiniteEtaleLocalResidueLift.nonempty
    (R := R) (Rh := R) (Ω := K) (e := RingEquiv.refl _) L⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_tensorProduct_isProduct_isNoetherianCompleteLocalRing
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : IsNoetherianCompleteLocalRing R)
    [Algebra R A] [Module.Finite R A] :
    ∃ (m : ℕ) (T : Fin m → Type u) (_ : ∀ i, CommRing (T i)),
      (∀ i, IsNoetherianCompleteLocalRing (T i)) ∧
      Nonempty ((A ⊗[R] A) ≃+* (Π i, T i)) := by
  let : Module.Finite R (A ⊗[R] A) := inferInstance
  exact finite_isProduct_isNoetherianCompleteLocalRing
    (S := A ⊗[R] A) hR

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensorProduct_spec_mem
    (B : BigFppfSite.{u}) {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (A ⊗[R] A))) := by
  have hAcard : Cardinal.mk A < B.cutoff :=
    lt_of_le_of_lt (le_max_right _ _) (by simpa [Scheme.size_Spec] using hA)
  have hbound :
      max Cardinal.aleph0 (max (Cardinal.mk A) (Cardinal.mk A)) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt hAcard hAcard)
  change (Spec (.of (A ⊗[R] A))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_tensorProduct_le.trans_lt hbound)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem isLocalHom_algebraMap_of_finite_local
    {R A : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Module.Finite R A] :
    IsLocalHom (algebraMap R A) :=
  ((IsLocalRing.local_hom_TFAE (algebraMap R A)).out 1 5).mpr
    (IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.under R (IsLocalRing.maximalIdeal A)))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exists_finite_etale_NCLR_residue_extension
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] :
    ∃ (L : IsLocalRing.FiniteIntermediateField.{u, u}
        (IsLocalRing.ResidueField R) K)
      (A : IsLocalRing.FiniteEtaleLocalResidueLift.{u, u, u} R R K
        (RingEquiv.refl _) L),
      IsNoetherianCompleteLocalRing A.carrier := by
  let : IsLocalRing R := hR.isLocal
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hR.isComplete
  let : HenselianLocalRing R :=
    henselianLocalRing_of_isAdicComplete_maximalIdeal R
  obtain ⟨L, hA⟩ := exists_finiteEtaleLocalResidueLift (R := R) K
  refine ⟨L, Classical.choice hA, ?_⟩
  exact IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing hR

/-- In the `m`-adic topology, an ideal between a power of `m` and `m` is a weak ideal of
definition. -/
private lemma adic_isWeakIdealOfDefinition {R : Type*} [CommRing R] (m J : Ideal R) {n : ℕ}
    (hn : m ^ n ≤ J) (hJ : J ≤ m) :
    letI : TopologicalSpace R := m.adicTopology
    TopologicalRing.IsWeakIdealOfDefinition J := by
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  refine ⟨J.toAddSubgroup.isOpen_of_mem_nhds
    (m.hasBasis_nhds_zero_adic.mem_iff.2 ⟨n, trivial, hn⟩), fun x hx => ?_⟩
  change Tendsto (fun k : ℕ => x ^ k) atTop (nhds 0)
  rw [atTop_basis.tendsto_iff m.hasBasis_nhds_zero_adic]
  exact fun k _ =>
    ⟨k, trivial, fun l hl => (Ideal.pow_le_pow_right hl) (Ideal.pow_mem_pow (hJ hx) l)⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma weaklyAdmissible_adic_of_completeLocal
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R) :
    letI : TopologicalSpace R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    TopologicalRing.IsWeaklyAdmissible R := by
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have hmweak : TopologicalRing.IsWeakIdealOfDefinition m :=
    adic_isWeakIdealOfDefinition m m (pow_one m).le le_rfl
  have hCT2 : CompleteSpace R ∧ T2Space R :=
    (IsAdic.isAdicComplete_iff (show IsAdic m from rfl)).mp hR.isComplete
  exact ⟨⟨m, hmweak⟩, hCT2.1, hCT2.2⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma completeLocal_topology_eq_adic_of_cofinal
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    (inferInstance : TopologicalSpace R) =
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology := by
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let top₀ : TopologicalSpace R := inferInstance
  obtain ⟨J, hJm⟩ := hD₂ 1
  have hJopen : IsOpen (J.1 : Set R) := J.2.1
  have hpowOpen : ∀ n : ℕ, IsOpen ((m ^ n : Ideal R) : Set R) := by
    intro n
    obtain ⟨K, hKm⟩ := hD₂ n
    exact (K.1.toAddSubgroup).isOpen_mono
      (show K.1.toAddSubgroup ≤ (m ^ n).toAddSubgroup by exact hKm) K.2.1
  have hcofinal : ∀ U ∈ @nhds R top₀ 0,
      ∃ n : ℕ, ((m ^ n : Ideal R) : Set R) ⊆ U := by
    intro U hU
    obtain ⟨K, hKn, hKU⟩ := (IsLinearTopology.hasBasis_ideal (R := R)).mem_iff.mp hU
    have hLweak : TopologicalRing.IsWeakIdealOfDefinition (K ⊓ J.1) :=
      ⟨(K.toAddSubgroup.isOpen_of_mem_nhds hKn).inter hJopen, fun x hx => J.2.2 x hx.2⟩
    obtain ⟨n, hn⟩ := hD₁ ⟨_, hLweak⟩
    refine ⟨n, ?_⟩
    intro x hx
    exact hKU (le_trans hn inf_le_left hx)
  have hzero : @nhds R top₀ 0 = @nhds R m.adicTopology 0 := by
    apply le_antisymm
    · intro U hU
      obtain ⟨n, -, hn⟩ := m.hasBasis_nhds_zero_adic.mem_iff.mp hU
      exact Filter.mem_of_superset
        ((hpowOpen n).mem_nhds (show (0 : R) ∈ (m ^ n : Ideal R) from (m ^ n).zero_mem)) hn
    · intro U hU
      obtain ⟨n, hn⟩ := hcofinal U hU
      exact (m.hasBasis_nhds_zero_adic.mem_iff).2 ⟨n, trivial, hn⟩
  apply TopologicalSpace.ext_nhds
  intro x
  let oldAdd : @IsTopologicalAddGroup R top₀ inferInstance := inferInstance
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  let adicAdd : @IsTopologicalAddGroup R m.adicTopology inferInstance := inferInstance
  calc
    @nhds R top₀ x = Filter.map (fun y : R => x + y) (@nhds R top₀ 0) :=
      (@map_add_left_nhds_zero R top₀ inferInstance oldAdd x).symm
    _ = Filter.map (fun y : R => x + y) (@nhds R m.adicTopology 0) := by rw [hzero]
    _ = @nhds R m.adicTopology x :=
      @map_add_left_nhds_zero R m.adicTopology inferInstance adicAdd x

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma maximalIdeal_succ_pow_isWeakIdealOfDefinition
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (n : ℕ) :
    TopologicalRing.IsWeakIdealOfDefinition
      ((@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1)) := by
  rename_i t _ _
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  have htop : t = m.adicTopology := completeLocal_topology_eq_adic_of_cofinal hR hD₁ hD₂
  subst htop
  exact adic_isWeakIdealOfDefinition m _ le_rfl (Ideal.pow_le_self (Nat.succ_ne_zero n))

attribute [-instance] CategoryTheory.catToReflQuiver in
private def maximalIdealPowerWeakIdeal
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (n : ℕ) : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨(@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1),
    maximalIdeal_succ_pow_isWeakIdealOfDefinition hR hD₁ hD₂ n⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def maximalIdealPowerIndexFunctor
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    ℕ ⥤ OrderDual
      { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } := by
  have hmono : Monotone (fun n : ℕ => OrderDual.toDual
      (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)) := by
    intro n k hnk
    change (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (k + 1) ≤
      (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1)
    exact Ideal.pow_le_pow_right (I := @IsLocalRing.maximalIdeal R _ hR.isLocal)
      (Nat.add_le_add_right hnk 1)
  exact hmono.functor

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma maximalIdealPowerIndexFunctor_final
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    (maximalIdealPowerIndexFunctor hR hD₁ hD₂).Final := by
  apply (Monotone.final_functor_iff (maximalIdealPowerIndexFunctor hR hD₁ hD₂).monotone).2
  intro J
  obtain ⟨n, hn⟩ := hD₁ J
  refine ⟨n, ?_⟩
  change (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1) ≤ J.1
  exact le_trans
    (Ideal.pow_le_pow_right (I := @IsLocalRing.maximalIdeal R _ hR.isLocal)
      (Nat.le_succ n)) hn

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_formalSpectrumMap_of_cofinalSequence
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (D : QuotientSystem B S hS R)
    (J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hmono : ∀ n, J (n + 1) ≤ J n)
    (hcofinal : ∀ I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, J n ≤ I)
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (x : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (J n)) ⟶ Y)
    (hx : ∀ n,
      (formalSpectrumDiagram D).map
        (homOfLE (hmono n)) ≫ x (n + 1) = x n) :
    ∃ q : formalSpectrum D ⟶ Y,
      ∀ n, formalSpectrumInclusion D (OrderDual.toDual (J n)) ≫ q = x n := by
  have hJ : ∀ {n k : ℕ}, n ≤ k → J k ≤ J n := by
    intro n k h
    induction k, h using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans (hmono k) ih
  have hPmono : Monotone fun n => OrderDual.toDual (J n) := by
    intro n k h
    change J k ≤ J n
    exact hJ h
  let P := hPmono.functor
  have hfinal : P.Final :=
    (Monotone.final_functor_iff hPmono).2 fun I => (hcofinal I).imp fun _ hn => hn
  let G := formalSpectrumDiagram D
  let H := P ⋙ G
  have hnat (n k : ℕ) (h : n ≤ k) : H.map (homOfLE h) ≫ x k = x n := by
    induction k, h using Nat.le_induction with
    | base => simp [H]
    | succ k hk ih =>
      have hcat : homOfLE hk ≫ homOfLE (Nat.le_succ k) =
          homOfLE (hk.trans (Nat.le_succ k)) := Subsingleton.elim _ _
      have hstep : H.map (homOfLE (Nat.le_succ k)) ≫ x (k + 1) = x k := by
        change G.map (P.map (homOfLE (Nat.le_succ k))) ≫ x (k + 1) = x k
        have hPstep : P.map (homOfLE (Nat.le_succ k)) =
            homOfLE (show (J (k + 1)).1 ≤ (J k).1 from hmono k) :=
          Subsingleton.elim _ _
        rw [hPstep]
        change (formalSpectrumDiagram D).map
          (homOfLE (hmono k)) ≫ x (k + 1) = x k
        exact hx k
      rw [← hcat, Functor.map_comp, Category.assoc, hstep, ih]
  let c : Cocone H := {
    pt := Y
    ι := {
      app := x
      naturality := by
        intro n k f
        have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
        rw [hf]
        exact hnat n k (leOfHom f)
    }
  }
  let q := (Functor.Final.colimitIso P G).inv ≫ colimit.desc H c
  refine ⟨q, ?_⟩
  intro n
  change formalSpectrumInclusion D (P.obj n) ≫
    ((Functor.Final.colimitIso P G).inv ≫ colimit.desc H c) = x n
  rw [← Category.assoc]
  change (colimit.ι G (P.obj n) ≫ (Functor.Final.colimitIso P G).inv) ≫
    colimit.desc H c = x n
  rw [Functor.Final.ι_colimitIso_inv P G n]
  exact colimit.ι_desc c n

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A compatible family over the maximal-ideal-power stages determines a map
from the formal spectrum. The powers are final in the weak-ideal index, so the
construction does not depend on choosing representatives at every weak ideal. -/
private theorem formalSpectrumMapOfMaximalIdealPowerStages
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (D : QuotientSystem B S hS R)
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (x : ∀ n, (formalSpectrumDiagram D).obj
      ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).obj n) ⟶ Y)
    (hx : ∀ n, (formalSpectrumDiagram D).map
      ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).map (homOfLE (Nat.le_succ n))) ≫
        x (n + 1) = x n) :
    ∃ q : formalSpectrum D ⟶ Y,
      ∀ n, formalSpectrumInclusion D
        ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).obj n) ≫ q = x n := by
  exact exists_formalSpectrumMap_of_cofinalSequence D (maximalIdealPowerWeakIdeal hR hD₁ hD₂)
    (fun n => Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
    (fun I => (hD₁ I).imp fun n hn => (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn) Y x hx

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma formalSpectrum_hom_ext_of_maximalIdealPowers
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (D : QuotientSystem B S hS R)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {f g : formalSpectrum D ⟶ Y}
    (h : ∀ n, formalSpectrumInclusion D
      ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).obj n) ≫ f =
      formalSpectrumInclusion D
        ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).obj n) ≫ g) :
    f = g := by
  let P := maximalIdealPowerIndexFunctor hR hD₁ hD₂
  let G := formalSpectrumDiagram D
  let H := P ⋙ G
  change colimit G ⟶ Y at f
  change colimit G ⟶ Y at g
  let : P.Final := maximalIdealPowerIndexFunctor_final hR hD₁ hD₂
  have hcomp : (Functor.Final.colimitIso P G).hom ≫ f =
      (Functor.Final.colimitIso P G).hom ≫ g := by
    apply colimit.hom_ext
    intro n
    have hstage : colimit.ι H n ≫ (Functor.Final.colimitIso P G).hom =
        formalSpectrumInclusion D (P.obj n) := by
      rw [Functor.Final.ι_colimitIso_hom P G n]
    calc
      colimit.ι H n ≫
          ((Functor.Final.colimitIso P G).hom ≫ f) =
          (colimit.ι H n ≫ (Functor.Final.colimitIso P G).hom) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = formalSpectrumInclusion D (P.obj n) ≫ f := by
        rw [hstage]
      _ = formalSpectrumInclusion D (P.obj n) ≫ g := h n
      _ = colimit.ι H n ≫
          ((Functor.Final.colimitIso P G).hom ≫ g) := by
        calc
          _ = (colimit.ι H n ≫ (Functor.Final.colimitIso P G).hom) ≫ g :=
            congrArg (fun k => k ≫ g) hstage |>.symm
          _ = _ := Category.assoc _ _ _
  exact (cancel_epi (Functor.Final.colimitIso P G).hom).mp hcomp

attribute [-instance] CategoryTheory.catToReflQuiver in
private def maximalIdealPowerStageTransition
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (D : QuotientSystem B S hS R) (n : ℕ) :
    D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n) ⟶
      D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ (n + 1)) :=
  D.transition <| Ideal.pow_le_pow_right (I := @IsLocalRing.maximalIdeal R _ hR.isLocal)
    (show n + 1 ≤ n + 2 by omega)

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma quotientFactor_kernel_squareZero
    {R : Type u} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (hJ : J ^ 2 ≤ I) : (RingHom.ker (Ideal.Quotient.factor hIJ)) ^ 2 = ⊥ := by
  rw [Ideal.Quotient.factor_ker hIJ, ← Ideal.map_pow]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    have hcomap : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
      ext x
      simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap]
    exact hJ
  · exact bot_le

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma specMap_ker_squareZero
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hker : (RingHom.ker f) ^ 2 = ⊥) :
    (Spec.map (CommRingCat.ofHom f)).ker ^ 2 = ⊥ := by
  let A : CommRingCat := CommRingCat.of R
  let B : CommRingCat := CommRingCat.of S
  let φ : A ⟶ B := CommRingCat.ofHom f
  let g := Spec.map φ
  let : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective φ hsurj
  apply Scheme.IdealSheafData.ext_of_isAffine (X := Spec A)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot]
  rw [Scheme.Hom.ker_apply]
  have hnat : (Scheme.ΓSpecIso B).hom.hom.comp g.appTop.hom =
      φ.hom.comp (Scheme.ΓSpecIso A).hom.hom :=
    congrArg (fun k : CommRingCat.Hom _ _ => k.hom)
      (Scheme.ΓSpecIso_naturality φ)
  have hkernel : RingHom.ker g.appTop.hom =
      (RingHom.ker f).comap (Scheme.ΓSpecIso A).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv,
      RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      hnat, ← RingHom.comap_ker]
    rfl
  change (RingHom.ker g.appTop.hom) ^ 2 = ⊥
  rw [hkernel]
  apply le_antisymm
  · calc
      (RingHom.ker f).comap (Scheme.ΓSpecIso A).hom.hom ^ 2 ≤
          ((RingHom.ker f) ^ 2).comap (Scheme.ΓSpecIso A).hom.hom :=
        Ideal.le_comap_pow (Scheme.ΓSpecIso A).hom.hom 2
      _ = ⊥ := by
        rw [hker]
        exact Ideal.comap_bot_of_injective _
          (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  · exact bot_le

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma maximalIdealPowerStageTransition_squareZero
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (D : QuotientSystem B S hS R) (n : ℕ) :
    Space.IsSquareZeroClosedImmersion B S hS
      (T := (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)).1)
      (T' := (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ (n + 1))).1)
      ((BigAffineFppf.inclusion B S hS).map
        (maximalIdealPowerStageTransition hR hD₁ hD₂ D n)) := by
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let I : Ideal R := m ^ (n + 1)
  let J : Ideal R := m ^ (n + 2)
  have hJI : J ≤ I := Ideal.pow_le_pow_right (I := m) (show n + 1 ≤ n + 2 by omega)
  have hI2 : I ^ 2 ≤ J := by
    simpa [I, J, pow_mul] using
      (Ideal.pow_le_pow_right (I := m) (show n + 2 ≤ (n + 1) * 2 by omega))
  have hfacSurj := Ideal.Quotient.factor_surjective hJI
  exact ⟨IsClosedImmersion.spec_of_surjective _ hfacSurj,
    specMap_ker_squareZero _ hfacSurj (quotientFactor_kernel_squareZero J I hJI hI2)⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma weaklyAdmissible_of_completeLocal_cofinal
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    TopologicalRing.IsWeaklyAdmissible R := by
  rename_i t _ _
  have htop : t = (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology :=
    completeLocal_topology_eq_adic_of_cofinal hR hD₁ hD₂
  subst t
  exact weaklyAdmissible_adic_of_completeLocal hR

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A single descending sequence of weak ideals is cofinal both for the
original quotient system and for the maximal-ideal-adic topology. -/
private lemma exists_common_cofinal_weakIdeals
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    ∃ J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      (∀ n, J (n + 1) ≤ J n) ∧
      (∀ n, (J n).1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1)) ∧
      (∀ I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
        ∃ n, J n ≤ I) := by
  classical
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let W : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    fun n => Classical.choose (hD₂ (n + 1))
  have hW (n : ℕ) : (W n).1 ≤ m ^ (n + 1) :=
    Classical.choose_spec (hD₂ (n + 1))
  let J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    Nat.rec (W 0) (fun n Jn =>
      ⟨Jn.1 ⊓ (W (n + 1)).1,
        TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right Jn.2 (W (n + 1)).2.1⟩)
  have hJmono : ∀ n, J (n + 1) ≤ J n := by
    intro n
    change (J n).1 ⊓ (W (n + 1)).1 ≤ (J n).1
    exact inf_le_left
  have hJbound : ∀ n, (J n).1 ≤ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact hW 0
    | succ n ih =>
      change (J n).1 ⊓ (W (n + 1)).1 ≤ m ^ (n + 1 + 1)
      exact le_trans inf_le_right (hW (n + 1))
  have hJcofinal : ∀ I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, J n ≤ I := by
    intro I
    obtain ⟨n, hn⟩ := hD₁ I
    refine ⟨n, ?_⟩
    change (J n).1 ≤ I.1
    calc
      (J n).1 ≤ m ^ (n + 1) := hJbound n
      _ ≤ m ^ n := Ideal.pow_le_pow_right (I := m) (Nat.le_succ n)
      _ ≤ I.1 := hn
  exact ⟨J, hJmono, hJbound, hJcofinal⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma commonCofinalIdeal_isWeak_adic
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : ∃ n > 0,
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n) :
    letI : TopologicalSpace R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    TopologicalRing.IsWeakIdealOfDefinition J.1 := by
  obtain ⟨n, hn⟩ := hD₁ J
  obtain ⟨k, hkpos, hkm⟩ := hJ
  exact adic_isWeakIdealOfDefinition _ J.1 hn (hkm.trans (Ideal.pow_le_self (by omega)))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma commonCofinalSequence_isWeak_adic
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hbound : ∀ n, (J n).1 ≤
      (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1)) :
    letI : TopologicalSpace R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    ∀ n, TopologicalRing.IsWeakIdealOfDefinition (J n).1 := by
  let top₀ : TopologicalSpace R := inferInstance
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  intro n
  exact @commonCofinalIdeal_isWeak_adic R _ top₀ hR hD₁ (J n)
    ⟨n + 1, by omega, hbound n⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma commonCofinalSequence_isCofinal_adicWeak
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (_hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (_hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (J : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hbound : ∀ n, (J n).1 ≤
      (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ (n + 1)) :
    letI : TopologicalSpace R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    ∀ K : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, (J n).1 ≤ K.1 := by
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  intro K
  have hKmem : (K.1 : Set R) ∈ nhds (0 : R) := K.2.1.mem_nhds K.1.zero_mem
  obtain ⟨k, -, hK⟩ := m.hasBasis_nhds_zero_adic.mem_iff.mp hKmem
  refine ⟨k, ?_⟩
  calc
    (J k).1 ≤ m ^ (k + 1) := hbound k
    _ ≤ m ^ k := Ideal.pow_le_pow_right (I := m) (Nat.le_succ k)
    _ ≤ K.1 := hK

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def adicQuotientSystem
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S) :
    letI : TopologicalSpace R :=
      (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    QuotientSystem B S hS R := by
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  letI : TopologicalSpace R := m.adicTopology
  refine ⟨?_, ?_, ?_⟩
  · intro J
    change (Spec (.of (R ⧸ J.1))).size < B.cutoff
    let f : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ J.1) :=
      CommRingCat.ofHom (Ideal.Quotient.mk J.1)
    have hclosed : IsClosedImmersion (Spec.map f) :=
      IsClosedImmersion.spec_of_surjective f Ideal.Quotient.mk_surjective
    exact Scheme.size_lt_of_isClosedImmersion (Spec.map f) hRS
  · intro J
    exact Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p
  · intro J L h
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.factor_comp_mk]

attribute [-instance] CategoryTheory.catToReflQuiver in
private def adicContinuousHom
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S) (f : R →+* A) [IsLocalHom f] :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
    ContinuousHom (adicQuotientSystem (hS := hS) hR hRS p)
      (adicQuotientSystem (hS := hS) hA hAS (Spec.map (CommRingCat.ofHom f) ≫ p)) := by
  letI : IsLocalRing R := hR.isLocal
  letI : IsLocalRing A := hA.isLocal
  let m := IsLocalRing.maximalIdeal R
  let n := IsLocalRing.maximalIdeal A
  letI : TopologicalSpace R := m.adicTopology
  letI : TopologicalSpace A := n.adicTopology
  letI : NonarchimedeanRing R := m.nonarchimedean
  letI : NonarchimedeanRing A := n.nonarchimedean
  refine ⟨f, ?_, ?_⟩
  · apply continuous_of_continuousAt_zero f
    rw [ContinuousAt, map_zero,
      m.hasBasis_nhds_zero_adic.tendsto_iff n.hasBasis_nhds_zero_adic]
    intro k _
    refine ⟨k, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) k
  · intro J K h
    change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f h)) ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
        (Spec.map (CommRingCat.ofHom f) ≫ p)
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 2

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exists_specMap_of_formalMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (p : Spec (.of A) ⟶ S)
    (hp : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)]
    (T : Scheme.{u}) (hT : B.Contains T) (tS : T ⟶ S)
    (q : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (Over.mk (ObjectProperty.homMk tS : B.obj hT ⟶ B.obj hS))) :
    ∃ f : (Over.mk p : Over S) ⟶ (Over.mk tS : Over S),
      ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        ∃ g : (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶
            Over.mk (ObjectProperty.homMk tS : B.obj hT ⟶ B.obj hS),
          B.inclusion.map g.left =
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left ∧
            formalSpectrumInclusion D (OrderDual.toDual J) ≫ q =
              (Sheaf.sheafifiedYoneda
                (BigFppfOver.topology B S hS)).map g := by
  obtain ⟨e, he, _⟩ :=
    existsUnique_equiv_specHom_formalSpectrumHom hA D p hp I hI T hT tS
  refine ⟨e.symm q, ?_⟩
  intro J
  obtain ⟨g, hg₁, hg₂⟩ := he (e.symm q) J
  refine ⟨g, hg₁, ?_⟩
  rwa [e.apply_symm_apply] at hg₂

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exists_siteMap_of_formalMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (p : Spec (.of A) ⟶ S)
    (hp : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)] (T : BigFppfOver B S hS)
    (q : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T) :
    ∃ t : (specOver hAS p).1 ⟶ T,
      ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        formalSpectrumInclusion D (OrderDual.toDual J) ≫ q =
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map
              (stageToSpec D hAS p J (hp J)) ≫ t) := by
  rcases T with ⟨⟨T, hT⟩, ⟨⟩, tS⟩
  obtain ⟨f, hf⟩ := exists_specMap_of_formalMap hA D p hp I hI T hT tS.hom q
  let t : (specOver hAS p).1 ⟶ Over.mk tS :=
    Over.homMk (ObjectProperty.homMk f.left) (ObjectProperty.hom_ext _ f.w)
  refine ⟨t, fun J => ?_⟩
  obtain ⟨g, hg, he⟩ := hf J
  rw [he]
  congr 1
  exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ hg)

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def algebraicSpaceSectionAtStage
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (D : QuotientSystem B S hS R)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    X.obj (Opposite.op ((D.stage J).1)) :=
  ULift.down (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
    (formalSpectrumInclusion D (OrderDual.toDual J) ≫ q))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma algebraicSpaceSectionAtStage_transition
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (D : QuotientSystem B S hS R)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX)
    (J L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : J.1 ≤ L.1) :
    X.map ((BigAffineFppf.inclusion B S hS).map (D.transition h)).op
      (algebraicSpaceSectionAtStage X hX D q J) =
        algebraicSpaceSectionAtStage X hX D q L := by
  let i := (BigAffineFppf.inclusion B S hS).map (D.transition h)
  have hcol :
      (formalSpectrumDiagram D).map (homOfLE h) ≫
          formalSpectrumInclusion D (OrderDual.toDual J) =
        formalSpectrumInclusion D (OrderDual.toDual L) :=
    colimit.w (formalSpectrumDiagram D) (homOfLE h)
  have hsec := Sheaf.sectionEquiv_map_comp
    (BigFppfOver.topology B S hS) i
      (formalSpectrumInclusion D (OrderDual.toDual J) ≫ q)
  have hdiagramMap :
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map i =
        (formalSpectrumDiagram D).map (homOfLE h) := rfl
  have harg :
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map i ≫
          (formalSpectrumInclusion D (OrderDual.toDual J) ≫ q) =
        formalSpectrumInclusion D (OrderDual.toDual L) ≫ q := by
    rw [hdiagramMap]
    exact (CategoryTheory.Category.assoc _ _ _).symm |>.trans
      (congrArg (fun k => k ≫ q) hcol)
  rw [harg] at hsec
  have hdown := congrArg ULift.down hsec
  have hmap (z : ULift (X.obj (Opposite.op ((D.stage J).1)))) :
      ULift.down ((upliftedSheaf X hX).obj.map i.op z) =
        X.map i.op z.down := rfl
  have hmap' := hmap (Sheaf.sectionEquiv
    (BigFppfOver.topology B S hS)
    (formalSpectrumInclusion D (OrderDual.toDual J) ≫ q))
  change ConcreteCategory.hom (X.map i.op)
      (ULift.down (Sheaf.sectionEquiv
        (BigFppfOver.topology B S hS)
        (formalSpectrumInclusion D (OrderDual.toDual J) ≫ q))) =
    ULift.down (Sheaf.sectionEquiv
      (BigFppfOver.topology B S hS)
      (formalSpectrumInclusion D (OrderDual.toDual L) ≫ q))
  exact hmap'.symm.trans hdown.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- An initial point of an étale atlas lifts to a compatible family over all
maximal-ideal-power quotients. -/
private lemma exists_compatible_etaleAtlas_powerStage_lifts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (D : QuotientSystem B S hS R)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : Space.FormallyEtale a)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX)
    (z₀ : (yoneda.obj U).obj (Opposite.op
      ((D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)).1)))
    (hz₀ : a.app (Opposite.op
      ((D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)).1)) z₀ =
        algebraicSpaceSectionAtStage X hX D q
          (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)) :
    ∃ z : ∀ n, (yoneda.obj U).obj (Opposite.op
        ((D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)).1)),
      z 0 = z₀ ∧
        (∀ n, (yoneda.obj U).map
          (Opposite.op ((BigAffineFppf.inclusion B S hS).map
            (maximalIdealPowerStageTransition hR hD₁ hD₂ D n))) (z (n + 1)) = z n) ∧
        (∀ n, a.app (Opposite.op
          ((D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)).1)) (z n) =
            algebraicSpaceSectionAtStage X hX D q
              (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)) := by
  let T : ℕ → BigFppfOver B S hS :=
    fun n => (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)).1
  let i : ∀ n, T n ⟶ T (n + 1) :=
    fun n => (BigAffineFppf.inclusion B S hS).map
      (maximalIdealPowerStageTransition hR hD₁ hD₂ D n)
  have hAff : ∀ n,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (T n)) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (T (n + 1))) := by
    intro n
    exact ⟨BigAffineFppf.isAffine_toScheme_obj B S hS
      (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)),
      BigAffineFppf.isAffine_toScheme_obj B S hS
      (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ (n + 1)))⟩
  have hSq : ∀ n, Space.IsSquareZeroClosedImmersion B S hS (i n) := by
    intro n
    exact maximalIdealPowerStageTransition_squareZero hR hD₁ hD₂ D n
  have hcompat : ∀ n, X.map (Opposite.op (i n))
      (algebraicSpaceSectionAtStage X hX D q
        (maximalIdealPowerWeakIdeal hR hD₁ hD₂ (n + 1))) =
      algebraicSpaceSectionAtStage X hX D q
        (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n) := by
    intro n
    apply algebraicSpaceSectionAtStage_transition X hX D q
  obtain ⟨z, hz0, hzcompat, hz⟩ := exists_compatible_formallyEtale_lifts
    B S hS a ha T i hAff hSq
    (fun n => algebraicSpaceSectionAtStage X hX D q
      (maximalIdealPowerWeakIdeal hR hD₁ hD₂ n)) hcompat z₀ hz₀
  exact ⟨z, hz0, hzcompat, hz⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_algebraicSpaceMap_of_residueAtlasLift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : Space.FormallyEtale a)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX)
    (z₀ : (D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)).1 ⟶ U)
    (hz₀ : a.app (Opposite.op
      ((D.stage (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)).1)) z₀ =
        algebraicSpaceSectionAtStage X hX D q
          (maximalIdealPowerWeakIdeal hR hD₁ hD₂ 0)) :
    ∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶
          upliftedSheaf X hX,
      formalSpectrumToSpec D hRS p hp ≫ f = q := by
  classical
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let J := maximalIdealPowerWeakIdeal hR hD₁ hD₂
  obtain ⟨z, hz0, hzc, hza⟩ := exists_compatible_etaleAtlas_powerStage_lifts
    B S hS hR hD₁ hD₂ D hX U a ha q z₀ hz₀
  have hmaps : ∀ n, (formalSpectrumDiagram D).map
      ((maximalIdealPowerIndexFunctor hR hD₁ hD₂).map (homOfLE (Nat.le_succ n))) ≫
        Y.map (z (n + 1)) = Y.map (z n) := by
    intro n
    change Y.map ((BigAffineFppf.inclusion B S hS).map
      (maximalIdealPowerStageTransition hR hD₁ hD₂ D n)) ≫
        Y.map (z (n + 1)) = Y.map (z n)
    rw [← Functor.map_comp]
    exact congrArg Y.map (hzc n)
  obtain ⟨qU, hqU⟩ := formalSpectrumMapOfMaximalIdealPowerStages
    hR hD₁ hD₂ D (Y.obj U) (fun n => Y.map (z n)) hmaps
  let hA := weaklyAdmissible_of_completeLocal_cofinal hR hD₁ hD₂
  let : IsLocalRing R := hR.isLocal
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hmweak : TopologicalRing.IsWeakIdealOfDefinition m := by
    simpa using maximalIdeal_succ_pow_isWeakIdealOfDefinition hR hD₁ hD₂ 0
  let : m.IsMaximal := by dsimp [m]; infer_instance
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  obtain ⟨t, htStage⟩ := exists_siteMap_of_formalMap
    hA D hRS p hp m hmweak U qU
  let f : Y.obj (specOver hRS p).1 ⟶ upliftedSheaf X hX :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
    (ULift.up (a.app (Opposite.op (specOver hRS p).1) t))
  refine ⟨f, ?_⟩
  apply formalSpectrum_hom_ext_of_maximalIdealPowers hR hD₁ hD₂ D
  intro n
  change formalSpectrumInclusion D (OrderDual.toDual (J n)) ≫ _ = _
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [formalSpectrumToSpec_spec]
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  refine Eq.trans (Sheaf.sectionEquiv_map_comp
    (BigFppfOver.topology B S hS)
    ((BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (J n) (hp (J n)))) f) ?_
  apply ULift.ext
  have hf : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) f =
      ULift.up (a.app (Opposite.op (specOver hRS p).1) t) :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply _
  rw [hf]
  change X.map _ (a.app _ t) = algebraicSpaceSectionAtStage X hX D q (J n)
  have ht : (BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (J n) (hp (J n))) ≫ t = z n := by
    have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
    exact (Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)).map_injective
      ((htStage (J n)).symm.trans (hqU n))
  have hnat := congrArg (fun v => v t) (a.naturality
    ((BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (J n) (hp (J n)))).op)
  have htz : a.app _ ((BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (J n) (hp (J n))) ≫ t) =
      algebraicSpaceSectionAtStage X hX D q (J n) := by
    rw [ht]
    exact hza n
  exact hnat.symm.trans htz

/-- Two sections which agree after restriction along a split epimorphism `π` are equal. -/
private theorem eq_of_map_eq_of_comp_eq_id {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*}
    {U V : C} (π : V ⟶ U) (t : U ⟶ V) (ht : t ≫ π = 𝟙 U) {x y : F.obj (op U)}
    (h : F.map π.op x = F.map π.op y) : x = y := by
  simpa [← Functor.map_comp_apply, ← op_comp, ht] using congrArg (F.map t.op) h

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_compatible_diagonal_lifts
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (x y : X.obj (Opposite.op U))
    {ι : Type*} (V : ι → BigFppfOver B S hS) (i : ∀ a, V a ⟶ U)
    (hxy : ∀ a, X.map (i a).op x = X.map (i a).op y) :
    ∃ (T : BigFppfOver B S hS) (π : T ⟶ U) (l : ∀ a, V a ⟶ T),
      (∀ a, l a ≫ π = i a) ∧ (∀ a b (k : V a ⟶ V b), k ≫ i b = i a → k ≫ l b = l a) ∧
      X.map π.op x = X.map π.op y := by
  let qx : yoneda.obj U ⟶ X := yonedaEquiv.symm x
  let qy : yoneda.obj U ⟶ X := yonedaEquiv.symm y
  let pair := prod.lift qx qy
  let d := hX.diagonal_representable
  let T := d.pullback pair
  let π := d.snd pair
  let hp := d.isPullback pair
  let r a : yoneda.obj (V a) ⟶ X := yoneda.map (i a) ≫ qx
  have hr a : r a = yoneda.map (i a) ≫ qy := by
    dsimp [r, qx, qy]
    rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, hxy a]
  have hw a : r a ≫ diag X = yoneda.map (i a) ≫ pair := by
    apply prod.hom_ext
    · simp [r, pair]
    · simpa [pair] using hr a
  let l a : V a ⟶ T := yonedaEquiv (hp.lift (r a) (yoneda.map (i a)) (hw a))
  have hl a : yoneda.map (l a) = hp.lift (r a) (yoneda.map (i a)) (hw a) := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
  have hl₁ a : yoneda.map (l a) ≫ d.fst pair = r a := by
    rw [hl]
    exact hp.lift_fst _ _ _
  have hl₂ a : yoneda.map (l a) ≫ yoneda.map π = yoneda.map (i a) := by
    rw [hl]
    exact hp.lift_snd _ _ _
  refine ⟨T, π, l, ?_, ?_, ?_⟩
  · exact fun a => yoneda.map_injective ((yoneda.map_comp _ _).trans (hl₂ a))
  · intro a b k hk
    apply yoneda.map_injective
    rw [Functor.map_comp]
    apply hp.hom_ext
    · rw [Category.assoc, hl₁, hl₁]
      change yoneda.map k ≫ (yoneda.map (i b) ≫ qx) = yoneda.map (i a) ≫ qx
      rw [← Category.assoc, ← Functor.map_comp, hk]
    · rw [Category.assoc, hl₂, hl₂, ← Functor.map_comp, hk]
  · have hπ := comp_eq_comp_of_comp_diag_eq_lift _ _ _ _ hp.w
    simpa [qx, qy, yonedaEquiv_symm_naturality_left] using hπ

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma algebraicSpace_map_ext_of_quotientStages
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    {f g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶
          upliftedSheaf X hX}
    (hfg : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hRS p J (hp J))) ≫ f =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hRS p J (hp J))) ≫ g) :
    f = g := by
  classical
  let top₀ : TopologicalSpace R := inferInstance
  obtain ⟨J, hJmono, hJbound, hJcofinal⟩ :=
    @exists_common_cofinal_weakIdeals R _ top₀ hR hD₁ hD₂
  let KseqOld := J
  let m : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let topAdic : TopologicalSpace R := m.adicTopology
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  have hD₁a : ∀ K : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, m ^ n ≤ K.1 := by
    intro K
    have hmem : (K.1 : Set R) ∈ nhds (0 : R) := K.2.1.mem_nhds K.1.zero_mem
    obtain ⟨n, -, hpow⟩ := m.hasBasis_nhds_zero_adic.mem_iff.mp hmem
    exact ⟨n + 1, le_trans (Ideal.pow_le_pow_right (Nat.le_succ n)) hpow⟩
  have hJad : ∀ n, TopologicalRing.IsWeakIdealOfDefinition (J n).1 :=
    @commonCofinalSequence_isWeak_adic R _ top₀ hR hD₁ J hJbound
  let Kseq : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    fun n => ⟨(KseqOld n).1, hJad n⟩
  have hD₂a : ∀ n : ℕ,
      ∃ K : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }, K.1 ≤ m ^ n := by
    intro n
    refine ⟨⟨(J n).1, hJad n⟩, ?_⟩
    calc
      (J n).1 ≤ m ^ (n + 1) := hJbound n
      _ ≤ m ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
  let hA := weaklyAdmissible_adic_of_completeLocal hR
  have hmweak : TopologicalRing.IsWeakIdealOfDefinition m := by
    have hpow := maximalIdeal_succ_pow_isWeakIdealOfDefinition hR hD₁a hD₂a 0
    simpa [m] using hpow
  let Da := adicQuotientSystem (B := B) (S := S) (hS := hS) hR hRS p
  have hpa : ∀ K : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫ p = Da.overS K := by
    intro K
    rfl
  let U : BigFppfOver B S hS :=
    ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p))
  let secF : (upliftedSheaf X hX).obj.obj (Opposite.op U) :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) f
  let secG : (upliftedSheaf X hX).obj.obj (Opposite.op U) :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) g
  let x : X.obj (Opposite.op U) := ULift.down secF
  let y : X.obj (Opposite.op U) := ULift.down secG
  have hKmono : ∀ n, Kseq (n + 1) ≤ Kseq n := by
    intro n
    change (KseqOld (n + 1)).1 ≤ (KseqOld n).1
    exact hJmono n
  have hKcofinal : ∀ K : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, Kseq n ≤ K := by
    intro K
    have hcof := @commonCofinalSequence_isCofinal_adicWeak R _ top₀ hR hD₁ hD₂
      KseqOld hJbound
    exact hcof K
  have hUsite : ∀ n, B.Contains (Spec (.of (R ⧸ (Kseq n).1))) :=
    fun n => Da.inSite (Kseq n)
  let : TopologicalSpace R := top₀
  let stageToOld : ∀ n,
      (@QuotientSystem.stage B S hS R _ topAdic Da (Kseq n)) ⟶
        (@QuotientSystem.stage B S hS R _ top₀ D (KseqOld n)) := fun n =>
    ObjectProperty.homMk (Over.homMk (𝟙 _) (ObjectProperty.hom_ext _ (hp (KseqOld n)).symm))
  let V : ℕ → BigFppfOver B S hS := fun n =>
    (BigAffineFppf.inclusion B S hS).obj (D.stage (KseqOld n))
  let i : ∀ n, V n ⟶ U := fun n =>
    (BigAffineFppf.inclusion B S hS).map
      (stageToSpec D hRS p (KseqOld n) (hp (KseqOld n)))
  have hxy : ∀ n, X.map (i n).op x = X.map (i n).op y := by
    intro n
    exact map_section_eq_of_comp_eq _ _ (hfg (KseqOld n))
  let kOld (n : ℕ) : V n ⟶ V (n + 1) :=
    (BigAffineFppf.inclusion B S hS).map (D.transition (hJmono n))
  have hkOld (n : ℕ) : kOld n ≫ i (n + 1) = i n := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono n))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (KseqOld (n + 1)).1)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (KseqOld n).1))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  obtain ⟨T, π₂, lifts, hlifts_snd, htransition, hπ⟩ :=
    exists_compatible_diagonal_lifts hX U x y V i hxy
  have hstageTransition : ∀ n,
      (@QuotientSystem.transition B S hS R _ topAdic Da
        (Kseq (n + 1)) (Kseq n) (hKmono n)) ≫ stageToOld (n + 1) =
        stageToOld n ≫ D.transition (hJmono n) := by
    intro n
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hKmono n))) ≫
        𝟙 (Spec (.of (R ⧸ (Kseq (n + 1)).1))) =
      𝟙 (Spec (.of (R ⧸ (Kseq n).1))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono n)))
    rw [Category.comp_id, Category.id_comp]
  let : TopologicalSpace R := topAdic
  let targetSheaf :=
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T
  let stageMaps : ∀ n,
      (formalSpectrumDiagram Da).obj
          (OrderDual.toDual (Kseq n)) ⟶ targetSheaf := by
    intro n
    change (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj
          (@QuotientSystem.stage B S hS R _ topAdic Da (Kseq n))) ⟶
          targetSheaf
    exact (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (stageToOld n) ≫ lifts n)
  have hstageMaps : ∀ n,
      (formalSpectrumDiagram Da).map
          (homOfLE (hKmono n)) ≫ stageMaps (n + 1) = stageMaps n := by
    intro n
    change (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (@QuotientSystem.transition B S hS R _ topAdic Da
              (Kseq (n + 1)) (Kseq n) (hKmono n))) ≫
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map (stageToOld (n + 1)) ≫
              lifts (n + 1)) =
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (stageToOld n) ≫ lifts n)
    rw [← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← Functor.map_comp, hstageTransition,
      Functor.map_comp, Category.assoc, htransition _ _ _ (hkOld n)]
  obtain ⟨qT, hqT⟩ := exists_formalSpectrumMap_of_cofinalSequence
    Da Kseq hKmono hKcofinal targetSheaf stageMaps hstageMaps
  let : IsLocalRing R := hR.isLocal
  let : m.IsMaximal := by dsimp [m]; infer_instance
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  obtain ⟨t, htStage⟩ := exists_siteMap_of_formalMap
    hA Da hRS p hpa m hmweak T qT
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let c := formalSpectrumToSpec Da hRS p hpa
  let k : ∀ K, (Da.stage K).1 ⟶ U := fun K =>
    (BigAffineFppf.inclusion B S hS).map
      (stageToSpec Da hRS p K (hpa K))
  have ht : c ≫ Y.map t = qT := by
    apply colimit.hom_ext
    intro K
    calc formalSpectrumInclusion Da K ≫ (c ≫ Y.map t)
        = (formalSpectrumInclusion Da K ≫ c) ≫ Y.map t :=
          (Category.assoc _ _ _).symm
      _ = Y.map (k K) ≫ Y.map t :=
          congrArg (· ≫ Y.map t)
            (formalSpectrumToSpec_spec Da hRS p hpa K)
      _ = Y.map (k K ≫ t) := (Y.map_comp _ _).symm
      _ = formalSpectrumInclusion Da K ≫ qT := (htStage K).symm
  have hproj : qT ≫ Y.map π₂ = c := by
    apply colimit.hom_ext
    intro K
    obtain ⟨n, hn⟩ := hKcofinal K
    have hw := colimit.w (formalSpectrumDiagram Da) (homOfLE hn)
    change (formalSpectrumDiagram Da).map (homOfLE hn) ≫
      formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) =
        formalSpectrumInclusion Da K at hw
    change formalSpectrumInclusion Da K ≫ (qT ≫ Y.map π₂) =
      formalSpectrumInclusion Da K ≫ c
    have hreduce :
        formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) ≫
            (qT ≫ Y.map π₂) =
          formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) ≫ c := by
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hqT n]
      change stageMaps n ≫ Y.map π₂ =
        formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) ≫
          formalSpectrumToSpec Da hRS p hpa
      rw [formalSpectrumToSpec_spec]
      change Y.map (_ ≫ lifts n) ≫ Y.map π₂ = Y.map (k (Kseq n))
      rw [← Functor.map_comp]
      congr 1
      have hl : lifts n ≫ π₂ = i n := hlifts_snd n
      rw [Category.assoc, hl]
      exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Category.id_comp _))
    calc
      formalSpectrumInclusion Da K ≫ (qT ≫ Y.map π₂) =
          ((formalSpectrumDiagram Da).map (homOfLE hn) ≫
            formalSpectrumInclusion Da (OrderDual.toDual (Kseq n))) ≫
              (qT ≫ Y.map π₂) := by rw [hw]
      _ = (formalSpectrumDiagram Da).map (homOfLE hn) ≫
            (formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) ≫
              (qT ≫ Y.map π₂)) := Category.assoc _ _ _
      _ = (formalSpectrumDiagram Da).map (homOfLE hn) ≫
            (formalSpectrumInclusion Da (OrderDual.toDual (Kseq n)) ≫ c) :=
              congrArg
                (fun z => (formalSpectrumDiagram Da).map
                  (homOfLE hn) ≫ z) hreduce
      _ = formalSpectrumInclusion Da K ≫ c :=
            (Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ c) hw)
  have htp : t ≫ π₂ = 𝟙 U := by
    have hrestrict :
        restrictToFormalSpectrum Da p hpa U
          ((Over.post B.inclusion).map (t ≫ π₂)) =
        restrictToFormalSpectrum Da p hpa U
          ((Over.post B.inclusion).map (𝟙 U)) := by
      rw [restrictToFormalSpectrum_eq,
        restrictToFormalSpectrum_eq, Functor.map_comp,
        ← Category.assoc, ht, hproj]
      change c = c ≫ Y.map (𝟙 U)
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    have he := (bijective_map_into_affine hA Da p hpa
      (specOver hRS p)).1 hrestrict
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (congrArg (fun v => v.left) he))
  exact (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
    (ULift.ext (eq_of_map_eq_of_comp_eq_id π₂ t htp hπ))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_finite_separable_point_of_etale_surjective
    (k : Type u) [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))
    [Etale f] [Surjective f] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : Module.Finite k K) (_ : Algebra.IsSeparable k K)
      (v : Spec (.of K) ⟶ V),
      v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  obtain ⟨I, K, hKF, hKA, hKfin, hKsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp
      inferInstance
  let := hKF
  let := hKA
  let := hKfin
  let := hKsep
  obtain ⟨v, hv⟩ := (show Function.Surjective f from Surjective.surj)
    (IsLocalRing.closedPoint k)
  let i : I := ((sigmaMk (fun i => Spec (.of (K i)))).symm (e.hom v)).1
  refine ⟨K i, inferInstance, inferInstance, inferInstance, inferInstance,
    Sigma.ι (fun i => Spec (.of (K i))) i ≫ e.inv, ?_⟩
  rw [Category.assoc, ← he, e.inv_hom_id_assoc, Sigma.ι_desc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_finite_etale_residue_point
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    {V : Scheme.{u}} (f : V ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    [Etale f] [Surjective f] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : Algebra R A)
      (_ : IsLocalHom (algebraMap R A)) (_ : Module.Finite R A)
      (_ : Algebra.Etale R A) (_ : IsNoetherianCompleteLocalRing A)
      (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V),
      v ≫ f = Spec.map (CommRingCat.ofHom
        (IsLocalRing.ResidueField.map (algebraMap R A))) := by
  obtain ⟨K, hK, hRK, hfin, hsep, v, hv⟩ :=
    exists_finite_separable_point_of_etale_surjective (IsLocalRing.ResidueField R) f
  let := hK
  let := hRK
  let := hfin
  let := hsep
  obtain ⟨A, hA, hlocal, halg, hloc, hfinite, hetale, ⟨e⟩⟩ :=
    IsLocalRing.FiniteEtaleLocalResidueLift.exists_residueField_algEquiv R K
  let := hA
  let := hlocal
  let := halg
  let := hloc
  let := hfinite
  let := hetale
  refine ⟨A, hA, hlocal, halg, hloc, hfinite, hetale,
    IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing hR,
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ v, ?_⟩
  rw [Category.assoc, hv, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact e.symm.commutes x

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_finite_separable_atlas_lift
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (p : Spec (.of k) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (hsurj : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a)
    (hetale : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a)
    (x : X.obj (Opposite.op (specOver (hS := hS) hk p).1)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : Module.Finite k K) (_ : Algebra.IsSeparable k K)
      (hK : B.Contains (Spec (.of K)))
      (v : (specOver (hS := hS) hK
        (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p)).1 ⟶ U),
      a.app _ v = X.map (Over.homMk
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (by rfl)).op x := by
  let C := BigFppfOver.toScheme B S hS
  let g : yoneda.obj (specOver (hS := hS) hk p).1 ⟶ X := yonedaEquiv.symm x
  let T := hetale.rep.pullback g
  let t := hetale.rep.snd g
  let b : T ⟶ U := yoneda.preimage (hetale.rep.fst g)
  have hb : yoneda.map b = hetale.rep.fst g := yoneda.map_preimage _
  have : Etale (C.map t) := hetale.property_snd g
  have : Surjective (C.map t) :=
    hsurj.property g _ _ (hetale.rep.isPullback g)
  obtain ⟨K, hKF, hKA, hKfin, hKsep, v, hv⟩ :=
    @exists_finite_separable_point_of_etale_surjective k _ (C.obj T) (C.map t)
      (hetale.property_snd g) (hsurj.property g _ _ (hetale.rep.isPullback g))
  let := hKF
  let := hKA
  let := hKfin
  let := hKsep
  have hK : B.Contains (Spec (.of K)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      k K hk
  let V := (specOver (hS := hS) hK
    (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p)).1
  let j : V ⟶ (specOver (hS := hS) hk p).1 :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (by rfl)
  let v' : V ⟶ T := Over.homMk (ObjectProperty.homMk v) (by
    apply ObjectProperty.hom_ext
    change v ≫ T.hom.hom = _
    have ht := congrArg (fun z => z.hom) t.w
    change C.map t ≫ p = T.hom.hom at ht
    rw [← ht]
    exact (Category.assoc v (C.map t) p).symm.trans (congrArg (fun g => g ≫ p) hv))
  have hv' : v' ≫ t = j :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hv)
  refine ⟨K, hKF, hKA, hKfin, hKsep, hK, v' ≫ b, ?_⟩
  have hw := hetale.rep.w g
  rw [← hb] at hw
  have he := congrArg (fun z => yoneda.map v' ≫ z) hw
  rw [← Category.assoc, ← yoneda.map_comp, ← Category.assoc,
    ← yoneda.map_comp, hv'] at he
  have hh := congrArg yonedaEquiv he
  change a.app _ (v' ≫ b) = X.map j.op x at hh
  exact hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma bigFppf_singleton_mem
    (B : BigFppfSite.{u}) {V W : B.Schemes} (f : V ⟶ W)
    [Flat (B.inclusion.map f)] [Surjective (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)] :
    Sieve.generate (Presieve.singleton f) ∈ B.topology W := by
  let E : PreZeroHypercover.{u + 1} W := PreZeroHypercover.singleton f
  have hE : IsFppfCovering (κ := B.cutoff) ⟨W, E⟩ := by
    change Presieve.map B.inclusion E.presieve₀ ∈ Scheme.fppfPrecoverage _
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    exact Scheme.Hom.singleton_mem_fppfPrecoverage _
  obtain ⟨⟨W', E'⟩, hE', he⟩ := B.fppf_has_representative ⟨W, E⟩ hE
  obtain ⟨heq, he⟩ := he
  change W = W' at heq
  subst W'
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨E', ?_, hE'⟩
  exact (PreZeroHypercover.presieve₀_singleton f).symm.trans
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent he)

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma bigFppfOver_isSheafFor_singleton
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W : BigFppfOver B S hS} (f : V ⟶ W)
    [Flat ((BigFppfOver.toScheme B S hS).map f)]
    [Surjective ((BigFppfOver.toScheme B S hS).map f)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  have hcov : Sieve.generate (Presieve.singleton f) ∈
      (BigFppfOver.topology B S hS) W := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    let : Flat (B.inclusion.map f.left) :=
      ‹Flat ((BigFppfOver.toScheme B S hS).map f)›
    let : Surjective (B.inclusion.map f.left) :=
      ‹Surjective ((BigFppfOver.toScheme B S hS).map f)›
    let : LocallyOfFinitePresentation (B.inclusion.map f.left) :=
      ‹LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f)›
    refine B.topology.superset_covering (Sieve.generate_mono ?_) (bigFppf_singleton_mem B f.left)
    rintro V g ⟨⟩
    exact ⟨_, f, 𝟙 _, Presieve.singleton_self _, (Category.id_comp _).symm⟩
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSheafFor _ hcov

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_maximalIdealPower_weak
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    letI : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
    TopologicalRing.IsWeakIdealOfDefinition ((IsLocalRing.maximalIdeal R) ^ (n + 1)) := by
  exact adic_isWeakIdealOfDefinition _ _ le_rfl (Ideal.pow_le_self (Nat.succ_ne_zero n))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_weak_ideals_cofinal
    (R : Type u) [CommRing R] [IsLocalRing R] :
    letI : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
    (∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n ≤ J.1) ∧
    (∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (IsLocalRing.maximalIdeal R) ^ n) := by
  let m := IsLocalRing.maximalIdeal R
  let : TopologicalSpace R := m.adicTopology
  refine ⟨fun J => ?_, fun n => ⟨⟨m ^ (n + 1), adic_maximalIdealPower_weak R n⟩,
    Ideal.pow_le_pow_right (Nat.le_succ n)⟩⟩
  obtain ⟨n, -, hn⟩ := m.hasBasis_nhds_zero_adic.mem_iff.mp (J.2.1.mem_nhds J.1.zero_mem)
  exact ⟨n, hn⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma formalSpectrumToSpec_naturality_adic
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S) (f : R →+* A) [IsLocalHom f] :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
    let D := adicQuotientSystem (hS := hS) hR hRS p
    let E := adicQuotientSystem (hS := hS) hA hAS (Spec.map (CommRingCat.ofHom f) ≫ p)
    formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR)
        (adicContinuousHom hR hA hRS hAS p f) ≫
      formalSpectrumToSpec D hRS p (fun _ => rfl) =
    formalSpectrumToSpec E hAS (Spec.map (CommRingCat.ofHom f) ≫ p)
        (fun _ => rfl) ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Over.homMk
          (U := (specOver (hS := hS) hAS (Spec.map (CommRingCat.ofHom f) ≫ p)).1)
          (V := (specOver (hS := hS) hRS p).1)
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f))) (by rfl)) := by
  let : IsLocalRing R := hR.isLocal
  let : IsLocalRing A := hA.isLocal
  let m := IsLocalRing.maximalIdeal R
  let n := IsLocalRing.maximalIdeal A
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  let : TopologicalSpace A := n.adicTopology
  let D := adicQuotientSystem (hS := hS) hR hRS p
  let E := adicQuotientSystem (hS := hS) hA hAS (Spec.map (CommRingCat.ofHom f) ≫ p)
  let fc := adicContinuousHom (hS := hS) hR hA hRS hAS p f
  apply colimit.hom_ext
  intro K
  obtain ⟨k, hk⟩ := (adic_weak_ideals_cofinal A).1 K
  let J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨m ^ (k + 1), adic_maximalIdealPower_weak R k⟩
  have hJK : J.1 ≤ Ideal.comap f K.1 := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) (k + 1)).trans
      ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let t : (specOver (hS := hS) hAS (Spec.map (CommRingCat.ofHom f) ≫ p)).1 ⟶
      (specOver (hS := hS) hRS p).1 :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f))) (by rfl)
  let s := (BigAffineFppf.inclusion B S hS).map (fc.stageMap J K hJK)
  let j := (BigAffineFppf.inclusion B S hS).map
    (stageToSpec D hRS p J rfl)
  let k := (BigAffineFppf.inclusion B S hS).map
    (stageToSpec E hAS (Spec.map (CommRingCat.ofHom f) ≫ p) K rfl)
  have hsj : s ≫ j = k ≫ t := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f hJK)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫
        Spec.map (CommRingCat.ofHom f)
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let cD := formalSpectrumToSpec D hRS p (fun _ => rfl)
  let cE := formalSpectrumToSpec E hAS
    (Spec.map (CommRingCat.ofHom f) ≫ p) (fun _ => rfl)
  let M := formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR) fc
  let iJ := formalSpectrumInclusion D (OrderDual.toDual J)
  let iK := formalSpectrumInclusion E K
  have hM : iK ≫ M = Y.map s ≫ iJ :=
    formalSpectrumMap_spec (weaklyAdmissible_adic_of_completeLocal hR) fc J K hJK
  have hj : iJ ≫ cD = Y.map j := formalSpectrumToSpec_spec D hRS p _ J
  have hk' : iK ≫ cE = Y.map k := formalSpectrumToSpec_spec E hAS _ _ K
  change iK ≫ (M ≫ cD) = iK ≫ (cE ≫ Y.map t)
  calc
    iK ≫ (M ≫ cD) = (iK ≫ M) ≫ cD := (Category.assoc _ _ _).symm
    _ = (Y.map s ≫ iJ) ≫ cD := congrArg (fun f => f ≫ cD) hM
    _ = Y.map s ≫ (iJ ≫ cD) := Category.assoc _ _ _
    _ = Y.map s ≫ Y.map j := congrArg (fun f => Y.map s ≫ f) hj
    _ = Y.map (s ≫ j) := (Y.map_comp s j).symm
    _ = Y.map (k ≫ t) := congrArg Y.map hsj
    _ = Y.map k ≫ Y.map t := Y.map_comp k t
    _ = (iK ≫ cE) ≫ Y.map t := congrArg (fun f => f ≫ Y.map t) hk'.symm
    _ = iK ≫ (cE ≫ Y.map t) := Category.assoc _ _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private def adicContinuousHomOver
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S) (q : Spec (.of A) ⟶ S)
    (f : R →+* A) [IsLocalHom f] (hw : Spec.map (CommRingCat.ofHom f) ≫ p = q) :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
    ContinuousHom (adicQuotientSystem (hS := hS) hR hRS p)
      (adicQuotientSystem (hS := hS) hA hAS q) := by
  letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
  letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
  exact
  { toRingHom := f
    continuous := (adicContinuousHom (hS := hS) hR hA hRS hAS p f).continuous
    overS := by
      intro J K h
      subst q
      exact (adicContinuousHom (hS := hS) hR hA hRS hAS p f).overS J K h }

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma formalSpectrumToSpec_naturality_adic_over
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S) (q : Spec (.of A) ⟶ S)
    (f : R →+* A) [IsLocalHom f] (hw : Spec.map (CommRingCat.ofHom f) ≫ p = q) :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
    let D := adicQuotientSystem (hS := hS) hR hRS p
    let E := adicQuotientSystem (hS := hS) hA hAS q
    formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR)
        (adicContinuousHomOver hR hA hRS hAS p q f hw) ≫
      formalSpectrumToSpec D hRS p (fun _ => rfl) =
    formalSpectrumToSpec E hAS q (fun _ => rfl) ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Over.homMk (U := (specOver (hS := hS) hAS q).1)
          (V := (specOver (hS := hS) hRS p).1)
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f)))
          (by apply ObjectProperty.hom_ext; exact hw)) := by
  subst q
  exact formalSpectrumToSpec_naturality_adic hR hA hRS hAS p f

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_algebraicSpace_map_ext
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    {f g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      (specOver (hS := hS) hRS p).1 ⟶ upliftedSheaf X hX}
    (he : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      let D := adicQuotientSystem (hS := hS) hR hRS p
      formalSpectrumToSpec D hRS p (fun _ => rfl) ≫ f =
        formalSpectrumToSpec D hRS p (fun _ => rfl) ≫ g) : f = g := by
  let : IsLocalRing R := hR.isLocal
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  let D := adicQuotientSystem (hS := hS) hR hRS p
  apply algebraicSpace_map_ext_of_quotientStages B S hS hR D
    (adic_weak_ideals_cofinal R).1 (adic_weak_ideals_cofinal R).2 hRS p
    (fun _ => rfl) X hX
  intro J
  have hj := congrArg (fun q => formalSpectrumInclusion D
    (OrderDual.toDual J) ≫ q) he
  have hspec := formalSpectrumToSpec_spec D hRS p
    (fun _ => rfl) J
  replace hj := ((Category.assoc _ _ _).trans hj).trans (Category.assoc _ _ _).symm
  exact ((congrArg (fun z => z ≫ f) hspec).symm.trans hj).trans
    (congrArg (fun z => z ≫ g) hspec)

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_descent_compatibility
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    (hT : IsNoetherianCompleteLocalRing T)
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (hTS : B.Contains (Spec (.of T)))
    (pR : Spec (.of R) ⟶ S) (pA : Spec (.of A) ⟶ S) (pT : Spec (.of T) ⟶ S)
    (a : R →+* A) (b₁ b₂ : A →+* T) [IsLocalHom a] [IsLocalHom b₁] [IsLocalHom b₂]
    (ha : Spec.map (CommRingCat.ofHom a) ≫ pR = pA)
    (hb₁ : Spec.map (CommRingCat.ofHom b₁) ≫ pA = pT)
    (hb₂ : Spec.map (CommRingCat.ofHom b₂) ≫ pA = pT)
    (hab : b₁.comp a = b₂.comp a)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      (specOver (hS := hS) hAS pA).1 ⟶ upliftedSheaf X hX)
    (q : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      formalSpectrum (adicQuotientSystem (hS := hS) hR hRS pR) ⟶
        upliftedSheaf X hX)
    (hx : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      letI : NonarchimedeanRing R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
      letI : IsLinearTopology R R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
      letI : TopologicalSpace A :=
        (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
      formalSpectrumToSpec (adicQuotientSystem (hS := hS) hA hAS pA)
          hAS pA (fun _ => rfl) ≫ x =
        formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR)
          (adicContinuousHomOver hR hA hRS hAS pR pA a ha) ≫ q) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Over.homMk (U := (specOver (hS := hS) hTS pT).1)
          (V := (specOver (hS := hS) hAS pA).1)
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom b₁)))
          (by apply ObjectProperty.hom_ext; exact hb₁)) ≫ x =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (Over.homMk (U := (specOver (hS := hS) hTS pT).1)
          (V := (specOver (hS := hS) hAS pA).1)
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom b₂)))
          (by apply ObjectProperty.hom_ext; exact hb₂)) ≫ x := by
  let : IsLocalRing R := hR.isLocal
  let : IsLocalRing A := hA.isLocal
  let : IsLocalRing T := hT.isLocal
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (IsLocalRing.maximalIdeal R).nonarchimedean
  let : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  let : TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  let : NonarchimedeanRing A := (IsLocalRing.maximalIdeal A).nonarchimedean
  let : IsLinearTopology A A := (IsLocalRing.maximalIdeal A).isLinearTopology
  let : TopologicalSpace T := (IsLocalRing.maximalIdeal T).adicTopology
  let ca := adicContinuousHomOver (hS := hS) hR hA hRS hAS pR pA a ha
  let cb₁ := adicContinuousHomOver (hS := hS) hA hT hAS hTS pA pT b₁ hb₁
  let cb₂ := adicContinuousHomOver (hS := hS) hA hT hAS hTS pA pT b₂ hb₂
  have hc : Spec.map (CommRingCat.ofHom (b₁.comp a)) ≫ pR = pT := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha, hb₁]
  let cc := adicContinuousHomOver (hS := hS) hR hT hRS hTS pR pT (b₁.comp a) hc
  apply adic_algebraicSpace_map_ext hT hTS pT hX
  dsimp only
  rw [← Category.assoc, ← Category.assoc,
    ← formalSpectrumToSpec_naturality_adic_over hA hT hAS hTS
      pA pT b₁ hb₁, Category.assoc, hx, ← Category.assoc,
    formalSpectrumMap_comp (weaklyAdmissible_adic_of_completeLocal hR)
      (weaklyAdmissible_adic_of_completeLocal hA) ca cb₁ cc rfl,
    ← formalSpectrumToSpec_naturality_adic_over hA hT hAS hTS
      pA pT b₂ hb₂, Category.assoc, hx, ← Category.assoc,
    formalSpectrumMap_comp (weaklyAdmissible_adic_of_completeLocal hR)
      (weaklyAdmissible_adic_of_completeLocal hA) ca cb₂ cc hab]

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_finite_etale_atlas_residue_lift
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    (hk : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (p : Spec (.of (IsLocalRing.ResidueField R)) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (hsurj : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a)
    (hetale : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a)
    (x : X.obj (Opposite.op (specOver (hS := hS) hk p).1)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : Algebra R A)
      (_ : IsLocalHom (algebraMap R A)) (_ : Module.Finite R A)
      (_ : Algebra.Etale R A) (_ : IsNoetherianCompleteLocalRing A)
      (hK : B.Contains (Spec (.of (IsLocalRing.ResidueField A))))
      (v : (specOver (hS := hS) hK
        (Spec.map (CommRingCat.ofHom
          (IsLocalRing.ResidueField.map (algebraMap R A))) ≫ p)).1 ⟶ U),
      a.app _ v = X.map (Over.homMk
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
          (IsLocalRing.ResidueField.map (algebraMap R A))))) (by rfl)).op x := by
  obtain ⟨K, hKF, hKA, hKfin, hKsep, hK, v, hv⟩ :=
    exists_finite_separable_atlas_lift (IsLocalRing.ResidueField R) hk p
      U a hsurj hetale x
  let := hKF
  let := hKA
  let := hKfin
  let := hKsep
  obtain ⟨A, hAC, hAL, hAA, hAloc, hAfin, hAet, ⟨e⟩⟩ :=
    IsLocalRing.FiniteEtaleLocalResidueLift.exists_residueField_algEquiv R K
  let := hAC
  let := hAL
  let := hAA
  let := hAloc
  let := hAfin
  let := hAet
  let f := IsLocalRing.ResidueField.map (algebraMap R A)
  have he : e.symm.toRingHom.comp (algebraMap (IsLocalRing.ResidueField R) K) = f := by
    ext t
    exact e.symm.commutes t
  have hK' : B.Contains (Spec (.of (IsLocalRing.ResidueField A))) := by
    change (Spec (.of (IsLocalRing.ResidueField A))).size < B.cutoff
    have hsize : Cardinal.mk (IsLocalRing.ResidueField A) = Cardinal.mk K :=
      Cardinal.mk_congr e.toEquiv
    change (Spec (.of K)).size < B.cutoff at hK
    rw [Scheme.size_Spec] at hK
    simpa only [Scheme.size_Spec, hsize] using hK
  let V := (specOver (hS := hS) hK
    (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) K)) ≫ p)).1
  let V' := (specOver (hS := hS) hK' (Spec.map (CommRingCat.ofHom f) ≫ p)).1
  let j : V' ⟶ V := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom e.symm.toRingHom))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) K)) ≫ p) = _
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, he]
      rfl)
  let k : V ⟶ (specOver (hS := hS) hk p).1 := Over.homMk
    (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) K)))) (by rfl)
  let k' : V' ⟶ (specOver (hS := hS) hk p).1 := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f))) (by rfl)
  have hjk : j ≫ k = k' := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) K)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]
    rfl
  refine ⟨A, hAC, hAL, hAA, hAloc, hAfin, hAet,
    IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing hR, hK', j ≫ v, ?_⟩
  have hn := congrArg (fun z => z v) (a.naturality j.op)
  change a.app (Opposite.op V') (j ≫ v) = X.map j.op (a.app (Opposite.op V) v) at hn
  change a.app (Opposite.op V) v = X.map k.op x at hv
  change a.app (Opposite.op V') (j ≫ v) = X.map k'.op x
  rw [hn, hv]
  rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp, hjk]

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma algebraicSpaceSectionAtStage_formalSpectrumMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A]
    [TopologicalSpace R] [TopologicalSpace A]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    {D : QuotientSystem B S hS R}
    {E : QuotientSystem B S hS A} (fc : ContinuousHom D E)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : J.1 ≤ Ideal.comap fc.toRingHom K.1)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX) :
    algebraicSpaceSectionAtStage X hX E (formalSpectrumMap hR fc ≫ q) K =
      X.map ((BigAffineFppf.inclusion B S hS).map (fc.stageMap J K h)).op
        (algebraicSpaceSectionAtStage X hX D q J) := by
  have he := congrArg (fun z => Sheaf.sectionEquiv
    (BigFppfOver.topology B S hS) (z ≫ q))
      (formalSpectrumMap_spec hR fc J K h)
  replace he := ((congrArg (Sheaf.sectionEquiv
      (BigFppfOver.topology B S hS)) (Category.assoc _ _ _)).symm.trans
    he).trans (congrArg (Sheaf.sectionEquiv
      (BigFppfOver.topology B S hS)) (Category.assoc _ _ _))
  replace he := he.trans (Sheaf.sectionEquiv_map_comp
    (BigFppfOver.topology B S hS)
    ((BigAffineFppf.inclusion B S hS).map (fc.stageMap J K h)) _)
  exact congrArg ULift.down he

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A morphism out of the quotient stage at the maximal ideal, obtained from a
morphism out of the spectrum of the residue field. -/
private def stageHomOfResidueFieldLift
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    (E : QuotientSystem B S hS A)
    (hw : TopologicalRing.IsWeakIdealOfDefinition (IsLocalRing.maximalIdeal A))
    {hka : B.Contains (Spec (.of (IsLocalRing.ResidueField A)))}
    {g : Spec (.of (IsLocalRing.ResidueField A)) ⟶ S}
    {U : BigFppfOver B S hS}
    (v : (specOver (hS := hS) hka g).1 ⟶ U)
    (hg : g = E.overS ⟨IsLocalRing.maximalIdeal A, hw⟩) :
    (E.stage ⟨IsLocalRing.maximalIdeal A, hw⟩).1 ⟶ U :=
  Over.homMk (ObjectProperty.homMk v.left.hom)
    (ObjectProperty.hom_ext _ ((congrArg (fun z => z.hom) v.w).trans hg))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The quotient stage at the maximal ideal, viewed over the spectrum of the
residue field. -/
private def stageToResidueFieldSpec
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    (E : QuotientSystem B S hS A)
    (hw : TopologicalRing.IsWeakIdealOfDefinition (IsLocalRing.maximalIdeal A))
    (hka : B.Contains (Spec (.of (IsLocalRing.ResidueField A))))
    {g : Spec (.of (IsLocalRing.ResidueField A)) ⟶ S}
    (hg : g = E.overS ⟨IsLocalRing.maximalIdeal A, hw⟩) :
    (E.stage ⟨IsLocalRing.maximalIdeal A, hw⟩).1 ⟶
      (specOver (hS := hS) hka g).1 :=
  Over.homMk (ObjectProperty.homMk (𝟙 _)) (ObjectProperty.hom_ext _ ((Category.id_comp _).trans hg))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Composing the identification of the quotient stage with a morphism out of
the spectrum of the residue field gives the induced morphism on stages. -/
private lemma stageToResidueFieldSpec_comp
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    (E : QuotientSystem B S hS A)
    (hw : TopologicalRing.IsWeakIdealOfDefinition (IsLocalRing.maximalIdeal A))
    (hka : B.Contains (Spec (.of (IsLocalRing.ResidueField A))))
    {g : Spec (.of (IsLocalRing.ResidueField A)) ⟶ S}
    {U : BigFppfOver B S hS}
    (v : (specOver (hS := hS) hka g).1 ⟶ U)
    (hg : g = E.overS ⟨IsLocalRing.maximalIdeal A, hw⟩) :
    stageToResidueFieldSpec E hw hka hg ≫ v =
      stageHomOfResidueFieldLift E hw v hg :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Category.id_comp _))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma exists_adic_lift_after_finite_etale
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (R : Type u) [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (q : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      formalSpectrum (adicQuotientSystem (hS := hS) hR hRS p) ⟶
        upliftedSheaf X hX) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : Algebra R A)
      (_ : IsLocalHom (algebraMap R A)) (_ : Module.Finite R A)
      (_ : Algebra.Etale R A) (hA : IsNoetherianCompleteLocalRing A)
      (hAS : B.Contains (Spec (.of A)))
      (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (specOver (hS := hS) hAS
          (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p)).1 ⟶
        upliftedSheaf X hX),
      letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      letI : NonarchimedeanRing R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
      letI : IsLinearTopology R R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
      letI : TopologicalSpace A :=
        (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
      let pA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p
      formalSpectrumToSpec (adicQuotientSystem (hS := hS) hA hAS pA)
          hAS pA (fun _ => rfl) ≫ x =
        formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR)
          (adicContinuousHom hR hA hRS hAS p (algebraMap R A)) ≫ q := by
  classical
  let : IsLocalRing R := hR.isLocal
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (IsLocalRing.maximalIdeal R).nonarchimedean
  let : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  let D := adicQuotientSystem (hS := hS) hR hRS p
  let m : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨IsLocalRing.maximalIdeal R, by simpa using adic_maximalIdealPower_weak R 0⟩
  let x₀ := algebraicSpaceSectionAtStage X hX D q m
  obtain ⟨U, a, hsurj, hetale⟩ := hX.exists_atlas
  have ha := etale_atlas_formallyEtale B S hS hX U a hetale
  obtain ⟨A, hAC, hAL, hAA, hAloc, hAfin, hAet, hA, hka, v, hv⟩ :=
    exists_finite_etale_atlas_residue_lift R hR (D.inSite m) (D.overS m)
      U a hsurj hetale x₀
  let := hAC
  let := hAL
  let := hAA
  let := hAloc
  let := hAfin
  let := hAet
  let : TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  let : NonarchimedeanRing A := (IsLocalRing.maximalIdeal A).nonarchimedean
  let : IsLinearTopology A A := (IsLocalRing.maximalIdeal A).isLinearTopology
  have hAS : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R A hRS
  let pA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p
  let E := adicQuotientSystem (hS := hS) hA hAS pA
  have hwA : TopologicalRing.IsWeakIdealOfDefinition (IsLocalRing.maximalIdeal A) := by
    simpa using adic_maximalIdealPower_weak A 0
  let n : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨IsLocalRing.maximalIdeal A, hwA⟩
  let fc := adicContinuousHom (hS := hS) hR hA hRS hAS p (algebraMap R A)
  let qA := formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR) fc ≫ q
  have hmn : m.1 ≤ Ideal.comap fc.toRingHom n.1 :=
    Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le (algebraMap R A))
  have hrmap : Ideal.quotientMap n.1 (algebraMap R A) hmn =
      IsLocalRing.ResidueField.map (algebraMap R A) := by
    ext r
    rfl
  have hpA : Spec.map (CommRingCat.ofHom
        (IsLocalRing.ResidueField.map (algebraMap R A))) ≫ D.overS m = E.overS n := by
    rw [← hrmap]
    exact fc.overS m n hmn
  let v' : (E.stage n).1 ⟶ U := stageHomOfResidueFieldLift E hwA v hpA
  have hnsec : a.app _ v' = algebraicSpaceSectionAtStage X hX E qA n := by
    have hh := algebraicSpaceSectionAtStage_formalSpectrumMap
      (weaklyAdmissible_adic_of_completeLocal hR) fc m n hmn X hX q
    change algebraicSpaceSectionAtStage X hX E qA n =
      X.map ((BigAffineFppf.inclusion B S hS).map
        (fc.stageMap m n hmn)).op x₀ at hh
    rw [hh]
    let j := stageToResidueFieldSpec E hwA hka hpA
    have hjv : j ≫ v = v' := stageToResidueFieldSpec_comp E hwA hka v hpA
    have hnat := congrArg (fun z => z v) (a.naturality j.op)
    change a.app _ (j ≫ v) = X.map j.op (a.app _ v) at hnat
    replace hnat := (congrArg (fun w => a.app (Opposite.op (E.stage n).1) w) hjv).symm.trans hnat
    have hnat' := hnat.trans (congrArg (X.map j.op) hv)
    refine hnat'.trans ?_
    refine (X.map_comp_apply _ j.op x₀).symm.trans ?_
    refine (congrArg (fun m => X.map m x₀) (op_comp (f := j)).symm).trans ?_
    congr 2
  have hn : maximalIdealPowerWeakIdeal hA
      (adic_weak_ideals_cofinal A).1 (adic_weak_ideals_cofinal A).2 0 = n :=
    Subtype.ext (pow_one _)
  have hz : ∃ v₀ : (E.stage (maximalIdealPowerWeakIdeal hA
      (adic_weak_ideals_cofinal A).1 (adic_weak_ideals_cofinal A).2 0)).1 ⟶ U,
      a.app _ v₀ = algebraicSpaceSectionAtStage X hX E qA
        (maximalIdealPowerWeakIdeal hA
          (adic_weak_ideals_cofinal A).1 (adic_weak_ideals_cofinal A).2 0) := by
    rw [hn]
    exact ⟨v', hnsec⟩
  obtain ⟨v₀, hv₀⟩ := hz
  obtain ⟨x, hx⟩ := exists_algebraicSpaceMap_of_residueAtlasLift B S hS hA E
    (adic_weak_ideals_cofinal A).1 (adic_weak_ideals_cofinal A).2 hAS pA
    (fun _ => rfl) X hX U a ha qA v₀ hv₀
  exact ⟨A, hAC, hAL, hAA, hAloc, hAfin, hAet, hA, hAS, x, hx⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma algebraicSpace_section_ext_of_pi
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {ι : Type u} [Finite ι] (A : ι → Type u) [∀ i, CommRing (A i)]
    (hP : B.Contains (Spec (.of (Π i, A i))))
    (hA : ∀ i, B.Contains (Spec (.of (A i)))) (p : Spec (.of (Π i, A i)) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (x y : X.obj (Opposite.op (specOver (hS := hS) hP p).1))
    (he : ∀ i, X.map (Over.homMk (V := (specOver hP p).1)
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i))))
        (U := (specOver (hA i)
          (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i)) ≫ p)).1) (by rfl)).op x =
      X.map (Over.homMk (V := (specOver hP p).1)
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i))))
        (U := (specOver (hA i)
          (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i)) ≫ p)).1) (by rfl)).op y) :
    x = y := by
  let U := (specOver (hS := hS) hP p).1
  let V i := (specOver (hS := hS) (hA i)
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i)) ≫ p)).1
  let j (i) : V i ⟶ U := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Pi.evalRingHom A i)))) (by rfl)
  obtain ⟨T, π, l, hl, -, hπ⟩ := exists_compatible_diagonal_lifts hX U x y V j he
  let e := sigmaSpec (fun i ↦ CommRingCat.of (A i))
  have : IsIso e := by dsimp [e]; infer_instance
  let ls (i) : Spec (.of (A i)) ⟶ T.left.obj := (l i).left.hom
  let t₀ : Spec (.of (Π i, A i)) ⟶ T.left.obj :=
    inv e ≫ Sigma.desc ls
  have ht₀ : t₀ ≫ π.left.hom = 𝟙 _ := by
    apply (cancel_epi e).mp
    dsimp [t₀]
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
    refine Eq.trans ?_ (Category.comp_id e).symm
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    change Sigma.ι _ i ≫ (Sigma.desc ls ≫ π.left.hom) =
      Sigma.ι _ i ≫ sigmaSpec (fun i ↦ CommRingCat.of (A i))
    rw [Sigma.ι_desc_assoc, ι_sigmaSpec]
    exact congrArg (fun z ↦ z.left.hom) (hl i)
  let t : U ⟶ T := Over.homMk (ObjectProperty.homMk t₀) (by
    apply ObjectProperty.hom_ext
    change t₀ ≫ T.hom.hom = p
    rw [← congrArg (fun z ↦ z.hom) π.w]
    change t₀ ≫ π.left.hom ≫ p = p
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ p) ht₀).trans (Category.id_comp p)))
  exact eq_of_map_eq_of_comp_eq_id π t (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ht₀)) hπ

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma isLocalHom_of_finite {A T : Type u} [CommRing A] [CommRing T]
    [IsLocalRing A] [IsLocalRing T] (f : A →+* T) (hf : f.Finite) :
    IsLocalHom f := by
  let := f.toAlgebra
  let : Module.Finite A T := hf
  exact isLocalHom_algebraMap_of_finite_local

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma algebraicSpace_section_ext_of_product_equiv
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : Type u} [CommRing P] {ι : Type u} [Finite ι]
    (T : ι → Type u) [∀ i, CommRing (T i)] (e : P ≃+* Π i, T i)
    (hP : B.Contains (Spec (.of P))) (p : Spec (.of P) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (x y : X.obj (Opposite.op (specOver (hS := hS) hP p).1))
    (he : ∀ i (hT : B.Contains (Spec (.of (T i)))) (pT : Spec (.of (T i)) ⟶ S)
      (hw : Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom)) ≫ p = pT),
      let v : (specOver (hS := hS) hT pT).1 ⟶
          (specOver (hS := hS) hP p).1 :=
        Over.homMk (ObjectProperty.homMk (Spec.map
          (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))
            (by apply ObjectProperty.hom_ext; exact hw)
      X.map v.op x = X.map v.op y) : x = y := by
  let er := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso er := by
    change IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  have hP' : B.Contains (Spec (.of (Π i, T i))) := by
    change (Spec (.of (Π i, T i))).size < B.cutoff
    rw [Scheme.size_congr (asIso er)]
    exact hP
  let p' := er ≫ p
  let v : (specOver (hS := hS) hP' p').1 ⟶
      (specOver (hS := hS) hP p).1 :=
    Over.homMk (ObjectProperty.homMk er) (by rfl)
  have : IsIso v :=
    have : IsIso (B.inclusion.map v.left) := inferInstanceAs (IsIso er)
    isIso_of_isIso_inclusion_map_left v
  apply (CategoryTheory.mono_iff_injective (X.map v.op)).mp inferInstance
  have hT (i) : B.Contains (Spec (.of (T i))) := by
    let f := CommRingCat.ofHom (Pi.evalRingHom T i)
    have : IsClosedImmersion (Spec.map f) :=
      IsClosedImmersion.spec_of_surjective f (Function.surjective_eval i)
    exact Scheme.size_lt_of_isClosedImmersion (Spec.map f) hP'
  apply algebraicSpace_section_ext_of_pi T hP' hT p' hX
  intro i
  rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp]
  have hw : Spec.map (CommRingCat.ofHom (Pi.evalRingHom T i)) ≫ p' =
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom)) ≫ p := by
    simp only [p', er, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hh := he i (hT i) _ hw.symm
  dsimp only at hh
  convert hh using 1 <;> congr 4 <;>
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Spec.map_comp _ _).symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_finite_etale_lift_compatible
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    [IsLocalHom (algebraMap R A)] [Module.Finite R A]
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      (specOver (hS := hS) hAS
        (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p)).1 ⟶
          upliftedSheaf X hX)
    (q : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      formalSpectrum (adicQuotientSystem (hS := hS) hR hRS p) ⟶
        upliftedSheaf X hX)
    (hx : letI : TopologicalSpace R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
      letI : NonarchimedeanRing R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
      letI : IsLinearTopology R R :=
        (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
      letI : TopologicalSpace A :=
        (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
      let pA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p
      formalSpectrumToSpec (adicQuotientSystem (hS := hS) hA hAS pA)
          hAS pA (fun _ => rfl) ≫ x =
        formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR)
          (adicContinuousHom hR hA hRS hAS p (algebraMap R A)) ≫ q) :
    let U := (specOver (hS := hS) hAS
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p)).1
    let V := (specOver (hS := hS) hRS p).1
    let v : U ⟶ V := Over.homMk
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (by rfl)
    let z := (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) x).down
    ∀ (Z : BigFppfOver B S hS) (f g : Z ⟶ U),
      f ≫ v = g ≫ v → X.map f.op z = X.map g.op z := by
  classical
  let : IsLocalRing R := hR.isLocal
  let : IsLocalRing A := hA.isLocal
  let U := (specOver (hS := hS) hAS
    (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p)).1
  let pA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p
  let a := algebraMap R A
  let P := A ⊗[R] A
  let b₁ : A →+* P := Algebra.TensorProduct.includeLeftRingHom
  let b₂ : A →+* P := Algebra.TensorProduct.includeRight.toRingHom
  let pb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R A A)
  have hab : b₁.comp a = b₂.comp a := by
    ext r
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  have hfin₁ : b₁.Finite := (RingHom.finite_algebraMap).mpr inferInstance
  have hfin₂ : b₂.Finite := by
    have ht := (RingHom.Finite.of_surjective
      (Algebra.TensorProduct.comm R A A).toRingHom
      (Algebra.TensorProduct.comm R A A).surjective).comp hfin₁
    convert ht using 1
    ext t
    change 1 ⊗ₜ[R] t = (Algebra.TensorProduct.comm R A A) (t ⊗ₜ[R] 1)
    exact (Algebra.TensorProduct.comm_tmul R t 1).symm
  have hP : B.Contains (Spec (.of P)) := tensorProduct_spec_mem B hAS
  let pP := Spec.map (CommRingCat.ofHom b₁) ≫ pA
  let W := (specOver (hS := hS) hP pP).1
  let t₁ : W ⟶ U := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom b₁))) (by rfl)
  have hb₂ : Spec.map (CommRingCat.ofHom b₂) ≫ pA = pP := by
    dsimp [pA, pP]
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rw [hab]
  let t₂ : W ⟶ U := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom b₂)))
    (by apply ObjectProperty.hom_ext; exact hb₂)
  let z := (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) x).down
  have hz : X.map t₁.op z = X.map t₂.op z := by
    obtain ⟨m, T, hTC, hT, ⟨e⟩⟩ := finite_tensorProduct_isProduct_isNoetherianCompleteLocalRing
      (A := A) hR
    let := hTC
    let T' : ULift.{u} (Fin m) → Type u := fun i => T i.down
    let e' : P ≃+* Π i, T' i := e.trans (RingEquiv.piCongrLeft T Equiv.ulift).symm
    apply algebraicSpace_section_ext_of_product_equiv T' e' hP pP hX
    intro i hTi pTi hw
    let : IsLocalRing (T' i) := (hT i.down).isLocal
    let d := (Pi.evalRingHom T' i).comp e'.toRingHom
    have hd : d.Finite := RingHom.Finite.of_surjective d
      ((Function.surjective_eval i).comp e'.surjective)
    let c₁ := d.comp b₁
    let c₂ := d.comp b₂
    let : IsLocalHom c₁ := isLocalHom_of_finite c₁ (hd.comp hfin₁)
    let : IsLocalHom c₂ := isLocalHom_of_finite c₂ (hd.comp hfin₂)
    have hc₁ : Spec.map (CommRingCat.ofHom c₁) ≫ pA = pTi := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      exact hw
    have hc₂ : Spec.map (CommRingCat.ofHom c₂) ≫ pA = pTi := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hb₂]
      exact hw
    have hc : c₁.comp a = c₂.comp a := by
      change d.comp (b₁.comp a) = d.comp (b₂.comp a)
      rw [hab]
    have hh := adic_descent_compatibility hR hA (hT i.down) hRS hAS hTi
      p pA pTi a c₁ c₂ rfl hc₁ hc₂ hc hX x q hx
    have hs := map_section_eq_of_comp_eq _ _ hh
    dsimp only
    rw [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp,
      ← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp]
    convert hs using 1 <;> congr 4 <;>
      exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Spec.map_comp _ _).symm)
  dsimp only
  intro Z f g hfg
  have hs : f.left.hom ≫ Spec.map (CommRingCat.ofHom a) =
      g.left.hom ≫ Spec.map (CommRingCat.ofHom a) :=
    congrArg (fun k => k.left.hom) hfg
  let l₀ := pb.lift f.left.hom g.left.hom hs
  have hl₁ : l₀ ≫ Spec.map (CommRingCat.ofHom b₁) = f.left.hom := pb.lift_fst _ _ _
  have hl₂ : l₀ ≫ Spec.map (CommRingCat.ofHom b₂) = g.left.hom := pb.lift_snd _ _ _
  let l : Z ⟶ W := Over.homMk (ObjectProperty.homMk l₀) (by
    apply ObjectProperty.hom_ext
    change l₀ ≫ (Spec.map (CommRingCat.ofHom b₁) ≫ pA) = _
    rw [← Category.assoc, hl₁]
    exact congrArg (fun k => k.hom) f.w)
  have hlf : l ≫ t₁ = f :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl₁)
  have hlg : l ≫ t₂ = g :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl₂)
  have hh := congrArg (X.map l.op) hz
  simpa only [← ConcreteCategory.comp_apply, ← X.map_comp, ← op_comp, hlf, hlg] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma etale_surjective_spec_quotient
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] [Module.FaithfullyFlat R A] (I : Ideal R) :
    Etale (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map))) := by
  let : Algebra.Etale (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm
  let : Module.FaithfullyFlat (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    Module.FaithfullyFlat.of_linearEquiv _ _
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toLinearEquiv
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  · exact (surjective_iff _).mpr (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      ((RingHom.faithfullyFlat_algebraMap_iff).mpr
        (inferInstance : Module.FaithfullyFlat (R ⧸ I) (A ⧸ I.map (algebraMap R A))))).2

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_formalSpectrumMap_left_cancellable
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hR : IsNoetherianCompleteLocalRing R) (hA : IsNoetherianCompleteLocalRing A)
    [IsLocalHom (algebraMap R A)] [Algebra.Etale R A]
    (hRS : B.Contains (Spec (.of R))) (hAS : B.Contains (Spec (.of A)))
    (p : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    letI : NonarchimedeanRing R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).nonarchimedean
    letI : IsLinearTopology R R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).isLinearTopology
    letI : TopologicalSpace A := (@IsLocalRing.maximalIdeal A _ hA.isLocal).adicTopology
    let D := adicQuotientSystem (hS := hS) hR hRS p
    let _E := adicQuotientSystem (hS := hS) hA hAS
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p)
    let fc := adicContinuousHom (hS := hS) hR hA hRS hAS p (algebraMap R A)
    ∀ q₁ q₂ : formalSpectrum D ⟶ upliftedSheaf X hX,
      formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR) fc ≫ q₁ =
        formalSpectrumMap (weaklyAdmissible_adic_of_completeLocal hR) fc ≫ q₂ →
      q₁ = q₂ := by
  let : IsLocalRing R := hR.isLocal
  let : IsLocalRing A := hA.isLocal
  let : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (IsLocalRing.maximalIdeal R).nonarchimedean
  let : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  let : TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  let D := adicQuotientSystem (hS := hS) hR hRS p
  let fc := adicContinuousHom (hS := hS) hR hA hRS hAS p (algebraMap R A)
  dsimp only
  intro q₁ q₂ hq
  apply formalSpectrum_hom_ext_of_maximalIdealPowers hR
    (adic_weak_ideals_cofinal R).1 (adic_weak_ideals_cofinal R).2 D
  intro n
  let J := maximalIdealPowerWeakIdeal hR
    (adic_weak_ideals_cofinal R).1 (adic_weak_ideals_cofinal R).2 n
  have hK : TopologicalRing.IsWeakIdealOfDefinition (J.1.map (algebraMap R A)) := by
    change TopologicalRing.IsWeakIdealOfDefinition
      (((IsLocalRing.maximalIdeal R) ^ (n + 1)).map (algebraMap R A))
    rw [Ideal.map_pow, Algebra.FormallyUnramified.map_maximalIdeal]
    exact adic_maximalIdealPower_weak A n
  let K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1.map (algebraMap R A), hK⟩
  let v := (BigAffineFppf.inclusion B S hS).map
    (fc.stageMap J K Ideal.le_comap_map)
  have : Etale ((BigFppfOver.toScheme B S hS).map v) :=
    (etale_surjective_spec_quotient (A := A) J.1).1
  have : Surjective ((BigFppfOver.toScheme B S hS).map v) :=
    (etale_surjective_spec_quotient (A := A) J.1).2
  have hsep := Presieve.isSeparatedFor_singleton.mp
    (bigFppfOver_isSheafFor_singleton B S hS v hX.isSheaf).isSeparatedFor
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  apply ULift.ext
  apply hsep
  have hh := congrArg (fun q => formalSpectrumInclusion _ (OrderDual.toDual K) ≫ q) hq
  replace hh := ((Category.assoc _ _ _).trans hh).trans (Category.assoc _ _ _).symm
  rw [formalSpectrumMap_spec
    (weaklyAdmissible_adic_of_completeLocal hR) fc J K Ideal.le_comap_map] at hh
  replace hh := ((Category.assoc _ _ _).symm.trans hh).trans (Category.assoc _ _ _)
  exact map_section_eq_of_comp_eq v v hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma adic_restriction_surjective
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (R : Type u) [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    letI : TopologicalSpace R := (@IsLocalRing.maximalIdeal R _ hR.isLocal).adicTopology
    let D := adicQuotientSystem (hS := hS) hR hRS p
    Function.Surjective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (specOver (hS := hS) hRS p).1 ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec D hRS p (fun _ => rfl) ≫ f) := by
  let : IsLocalRing R := hR.isLocal
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  let : NonarchimedeanRing R := (IsLocalRing.maximalIdeal R).nonarchimedean
  let : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  let D := adicQuotientSystem (hS := hS) hR hRS p
  dsimp only
  intro q
  obtain ⟨A, hAC, hAL, hAA, hAloc, hAfin, hAet, hA, hAS, x, hx⟩ :=
    exists_adic_lift_after_finite_etale R hR hRS p hX q
  let := hAC
  let := hAL
  let := hAA
  let := hAloc
  let := hAfin
  let := hAet
  let : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let pA := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ p
  let U := (specOver (hS := hS) hAS pA).1
  let V := (specOver (hS := hS) hRS p).1
  let v : U ⟶ V := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (by rfl)
  have : Etale ((BigFppfOver.toScheme B S hS).map v) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  have : Surjective ((BigFppfOver.toScheme B S hS).map v) :=
    (surjective_iff _).mpr (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstance : Module.FaithfullyFlat R A))).2
  let z := (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) x).down
  obtain ⟨y, hy, _⟩ := (Presieve.isSheafFor_singleton.mp
    (bigFppfOver_isSheafFor_singleton B S hS v hX.isSheaf)) z
      (fun {Z} f g hfg => adic_finite_etale_lift_compatible
        hR hA hRS hAS p hX x q hx Z f g hfg)
  let f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶
      upliftedSheaf X hX :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (ULift.up y)
  have hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map v ≫ f = x := by
    apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
    rw [Sheaf.sectionEquiv_map_comp]
    have hfy : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) f =
        ULift.up y :=
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply _
    rw [hfy]
    exact ULift.ext hy
  refine ⟨f, ?_⟩
  apply adic_formalSpectrumMap_left_cancellable hR hA hRS hAS p hX
  rwa [← Category.assoc, formalSpectrumToSpec_naturality_adic hR hA hRS hAS p
      (algebraMap R A), Category.assoc, hf]

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma restriction_surjective_of_cofinal_adic
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD₂ : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (q : formalSpectrum D ⟶ upliftedSheaf X hX) :
    ∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (specOver (hS := hS) hRS p).1 ⟶ upliftedSheaf X hX,
      formalSpectrumToSpec D hRS p hp ≫ f = q := by
  let top₀ : TopologicalSpace R := inferInstance
  obtain ⟨J, hJmono, hJbound, hJcofinal⟩ :=
    exists_common_cofinal_weakIdeals hR hD₁ hD₂
  let m := @IsLocalRing.maximalIdeal R _ hR.isLocal
  let : TopologicalSpace R := m.adicTopology
  let : NonarchimedeanRing R := m.nonarchimedean
  let : IsLinearTopology R R := m.isLinearTopology
  have hJad : ∀ n, TopologicalRing.IsWeakIdealOfDefinition (J n).1 :=
    @commonCofinalSequence_isWeak_adic R _ top₀ hR hD₁ J hJbound
  let K : ℕ → { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    fun n => ⟨(J n).1, hJad n⟩
  have hKmono : ∀ n, K (n + 1) ≤ K n := hJmono
  have hKcofinal : ∀ L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n, K n ≤ L :=
    @commonCofinalSequence_isCofinal_adicWeak R _ top₀ hR hD₁ hD₂ J hJbound
  let Da := adicQuotientSystem (hS := hS) hR hRS p
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let v (n : ℕ) : (Da.stage (K n)).1 ⟶
      (@QuotientSystem.stage B S hS R _ top₀ D (J n)).1 :=
    Over.homMk (ObjectProperty.homMk (𝟙 _))
      (ObjectProperty.hom_ext _ ((Category.id_comp _).trans (hp (J n)).symm))
  have hv (n : ℕ) : IsIso (v n) :=
    have : IsIso (B.inclusion.map (v n).left) :=
      inferInstanceAs (IsIso (𝟙 (Spec (.of (R ⧸ (J n).1)))))
    isIso_of_isIso_inclusion_map_left (v n)
  let r (n : ℕ) := @formalSpectrumInclusion B S hS R _ top₀ D
    (OrderDual.toDual (J n)) ≫ q
  let stages (n : ℕ) : (formalSpectrumDiagram Da).obj
      (OrderDual.toDual (K n)) ⟶ upliftedSheaf X hX := Y.map (v n) ≫ r n
  have hstages (n : ℕ) : (formalSpectrumDiagram Da).map
      (homOfLE (hKmono n)) ≫ stages (n + 1) = stages n := by
    let a := (BigAffineFppf.inclusion B S hS).map (Da.transition (hKmono n))
    let b := (BigAffineFppf.inclusion B S hS).map
      (@QuotientSystem.transition B S hS R _ top₀ D (J (n + 1)) (J n) (hJmono n))
    have hvab : a ≫ v (n + 1) = v n ≫ b := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hKmono n))) ≫ 𝟙 _ =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hJmono n)))
      rw [Category.comp_id, Category.id_comp]
    have hb : Y.map b ≫ r (n + 1) = r n := by
      have hw := colimit.w (@formalSpectrumDiagram B S hS R _ top₀ D)
        (homOfLE (hJmono n))
      change Y.map b ≫ (@formalSpectrumInclusion B S hS R _ top₀ D
        (OrderDual.toDual (J (n + 1))) ≫ q) = _
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ q) hw)
    change Y.map a ≫ (Y.map (v (n + 1)) ≫ r (n + 1)) = Y.map (v n) ≫ r n
    calc
      _ = Y.map (a ≫ v (n + 1)) ≫ r (n + 1) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun g => g ≫ r (n + 1)) (Y.map_comp a (v (n + 1))).symm)
      _ = Y.map (v n ≫ b) ≫ r (n + 1) := congrArg (fun f => Y.map f ≫ r (n + 1)) hvab
      _ = Y.map (v n) ≫ (Y.map b ≫ r (n + 1)) :=
        (congrArg (fun g => g ≫ r (n + 1)) (Y.map_comp (v n) b)).trans
          (Category.assoc _ _ _)
      _ = Y.map (v n) ≫ r n := congrArg (fun f => Y.map (v n) ≫ f) hb
  obtain ⟨qa, hqa⟩ := exists_formalSpectrumMap_of_cofinalSequence Da K hKmono hKcofinal
    (upliftedSheaf X hX) stages hstages
  obtain ⟨f, hf⟩ := adic_restriction_surjective R hR hRS p hX qa
  refine ⟨f, ?_⟩
  have hn (n : ℕ) : @formalSpectrumInclusion B S hS R _ top₀ D
      (OrderDual.toDual (J n)) ≫
        (@formalSpectrumToSpec B S hS R _ top₀ D hRS p hp ≫ f) = r n := by
    let j := (BigAffineFppf.inclusion B S hS).map
      (@stageToSpec B S hS R _ top₀ D hRS p (J n) (hp (J n)))
    let k := (BigAffineFppf.inclusion B S hS).map
      (stageToSpec Da hRS p (K n) rfl)
    have hvj : v n ≫ j = k :=
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Category.id_comp _))
    have hj : @formalSpectrumInclusion B S hS R _ top₀ D
        (OrderDual.toDual (J n)) ≫
          @formalSpectrumToSpec B S hS R _ top₀ D hRS p hp = Y.map j :=
      @formalSpectrumToSpec_spec B S hS R _ top₀ D hRS p hp (J n)
    have hk : formalSpectrumInclusion Da (OrderDual.toDual (K n)) ≫
        formalSpectrumToSpec Da hRS p (fun _ => rfl) = Y.map k :=
      formalSpectrumToSpec_spec Da hRS p _ (K n)
    let := hv n
    have hstep : Y.map (v n) ≫ (Y.map j ≫ f) = Y.map k ≫ f :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f)
        ((Y.map_comp (v n) j).symm.trans (congrArg Y.map hvj)))
    have hstep₃ : Y.map k ≫ f =
        formalSpectrumInclusion Da (OrderDual.toDual (K n)) ≫
          (formalSpectrumToSpec Da hRS p (fun _ => rfl) ≫ f) :=
      (congrArg (fun g => g ≫ f) hk.symm).trans (Category.assoc _ _ _)
    have hstep₁ : Y.map (v n) ≫
          (@formalSpectrumInclusion B S hS R _ top₀ D
              (OrderDual.toDual (J n)) ≫
            (@formalSpectrumToSpec B S hS R _ top₀ D hRS p hp ≫
              f)) =
        Y.map (v n) ≫ (Y.map j ≫ f) :=
      congrArg (fun g => Y.map (v n) ≫ g)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) hj))
    have hstep₄ : formalSpectrumInclusion Da
            (OrderDual.toDual (K n)) ≫
          (formalSpectrumToSpec Da hRS p (fun _ => rfl) ≫ f) =
        formalSpectrumInclusion Da (OrderDual.toDual (K n)) ≫ qa :=
      congrArg (fun g => formalSpectrumInclusion Da
        (OrderDual.toDual (K n)) ≫ g) hf
    exact (cancel_epi (Y.map (v n))).mp
      (hstep₁.trans (hstep.trans (hstep₃.trans (hstep₄.trans (hqa n)))))
  apply colimit.hom_ext
  intro L
  obtain ⟨n, hnL⟩ := hJcofinal L
  let G := @formalSpectrumDiagram B S hS R _ top₀ D
  let iL := @formalSpectrumInclusion B S hS R _ top₀ D L
  let iN := @formalSpectrumInclusion B S hS R _ top₀ D
    (OrderDual.toDual (J n))
  let a := G.map (homOfLE hnL)
  let c := @formalSpectrumToSpec B S hS R _ top₀ D hRS p hp ≫ f
  have hw : a ≫ iN = iL := colimit.w G (homOfLE hnL)
  change iL ≫ c = iL ≫ q
  rw [← hw]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (hn n)).trans (Category.assoc _ _ _).symm)

/-- **The surjectivity half of Stacks 0AQH.** Restriction along the canonical map
`Spf R ⟶ Spec R` hits every morphism from the formal spectrum of a Noetherian complete local
`S`-algebra `R` to an algebraic space over `S`.

Both cofinality conditions on the weak ideals of definition are used, so that the formal
spectrum of the quotient system is the `𝔪`-adic one. -/
@[stacks 0AQH "surjectivity"]
public theorem surjective_map_into_algebraicSpace
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Surjective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec D hRS p hp ≫ f) :=
  fun q => restriction_surjective_of_cofinal_adic B S hS R hR D hD₁ hD hRS p hp X hX q

/-- **Stacks 0AQH.** For `R` a Noetherian complete local `S`-algebra and `X` an algebraic
space over `S`, restriction along `Spf R ⟶ Spec R` is a bijection
`Mor_S(Spec R, X) ⟶ Mor_S(Spf R, X)`. -/
@[stacks 0AQH]
public theorem bijective_map_into_algebraicSpace
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (p : Spec (.of R) ⟶ S)
    (hp : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Function.Bijective (fun f :
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS p)) ⟶ upliftedSheaf X hX =>
      formalSpectrumToSpec D hRS p hp ≫ f) :=
  ⟨injective_map_into_algebraicSpace hR D hD hRS p hp X hX,
    surjective_map_into_algebraicSpace hR D hD₁ hD hRS p hp X hX⟩

end AlgebraicGeometry.FormalSpace

end
