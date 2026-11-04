module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Descent
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.InverseImageComponents
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.InverseImageComponents
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalCrossingsAfterPointBlowups
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalCrossingsAfterPointBlowups
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.ResolutionInherited

/-!
# Chains of blowups at two-dimensional closed points

A *surface point blowup chain* over a scheme `X` is a finite composition
`Xₙ → Xₙ₋₁ → … → X₀ = X` in which each `Xᵢ₊₁ → Xᵢ` is the blowup of `Xᵢ` at a closed point whose
local ring is two-dimensional. On a regular Noetherian scheme of dimension two these are the
blowups that the global form of [Stacks, Tag 0AGR] and part (1) of [Stacks, Tag 0AGQ] are about:
the blowup is again regular of dimension two, and its exceptional fibre is a regular curve.

The principalization of [Stacks, Tag 0AHH] blows up only points of the support of an ideal sheaf
supported on finitely many closed points with regular two-dimensional local rings, so it produces
such a chain, and so does the proof of [Stacks, Tag 0BIB] built on it. Along such a chain over a
regular Noetherian surface, condition (3) of [Stacks, Tag 0BI4] — resolvability by blowups at
closed points — passes from the one-dimensional irreducible components of a closed subscheme to
the one-dimensional irreducible components of its inverse image: a component of the inverse image
is either a component of an exceptional fibre, which is regular, or the strict transform of a
component of the original subscheme, to which resolvability passes.

## Main definitions

* `Stacks.ResolutionOfSurfaces.SurfacePointBlowupChain` — a finite sequence of blowups at closed
  points whose local rings are two-dimensional, indexed by its composite morphism.

## Main results

* `Stacks.ResolutionOfSurfaces.SurfacePointBlowupChain.toPointBlowupChain` — such a chain is a
  point blowup chain with unrestricted centres.
* `Stacks.ResolutionOfSurfaces.SurfacePointBlowupChain.comp` — such chains compose.
* `Stacks.ResolutionOfSurfaces.SurfacePointBlowupChain.isRegular` — along such a chain a regular
  Noetherian scheme of dimension two stays regular of dimension two.
* `Stacks.ResolutionOfSurfaces.exists_surfacePointBlowupChain_isEffectiveCartierDivisor` — the
  colength induction of [Stacks, Tag 0AHH], along a chain of blowups at two-dimensional points.
* `Stacks.ResolutionOfSurfaces.exists_surfacePointBlowupChain_comap_isEffectiveCartierDivisor` —
  [Stacks, Tag 0BIB], along a chain of blowups at two-dimensional points.
* `Stacks.ResolutionOfSurfaces.resolvable_componentIdeal_comap_of_surfacePointBlowupChain` —
  resolvability of the one-dimensional components of a closed subscheme of a regular Noetherian
  surface passes to its inverse image along a chain of blowups at two-dimensional points.

## Implementation notes

The local splitting of [Stacks, Tag 0AGT] at the level of sheaves of ideals,
`Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent`, is an explicit argument of the two
principalization results, exactly as in the forms of Tags 0AHH and 0BIB they refine.

The dimension of the local ring at each centre is what the regularity of the exceptional fibre
needs: a closed point of a regular Noetherian scheme of dimension two can have a local ring of
dimension less than two, and there the blowup is empty or an isomorphism. Recording it in the
chain is what lets the inheritance of resolvability treat the exceptional components.

The component of an inverse image produced by the decomposition of `InverseImageComponents` is the
reduced strict transform `Stacks.ResolutionOfSurfaces.reducedStrictTransform`, while resolvability
is carried along `AlgebraicGeometry.transformIdeal`. The two agree on a reduced subscheme, since
the strict transform of a reduced subscheme is either isomorphic to it or the blowup of it at a
closed point, and so is reduced.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### Chains of blowups at two-dimensional closed points -/

/-- A finite sequence of blowups at closed points whose local rings are two-dimensional. -/
public inductive SurfacePointBlowupChain (X : Scheme.{u}) : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl : SurfacePointBlowupChain X X (𝟙 X)
  | step {W : Scheme.{u}} {h : W ⟶ X} (hh : SurfacePointBlowupChain X W h) (w : W)
      (hw : IsClosed ({w} : Set W)) (hdim : ringKrullDim (W.presheaf.stalk w) = 2) :
      SurfacePointBlowupChain X
        (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)

namespace SurfacePointBlowupChain

/-- A chain of blowups at two-dimensional closed points is a chain of blowups at closed points. -/
public theorem toPointBlowupChain {X Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : SurfacePointBlowupChain X Y f) : PointBlowupChain X Set.univ Y f := by
  induction hf with
  | refl => exact .refl
  | step hh w hw hdim ih => exact ih.step w hw (Set.mem_univ _)

/-- A chain of blowups at two-dimensional closed points over the source of another such chain
composes with it. -/
public theorem comp {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    (hf : SurfacePointBlowupChain X Y f) (hg : SurfacePointBlowupChain Y Z g) :
    SurfacePointBlowupChain X Z (g ≫ f) := by
  induction hg with
  | refl => simpa using hf
  | step hh w hw hdim ih =>
    rw [Category.assoc]
    exact ih.step w hw hdim

/-- A chain of blowups at two-dimensional closed points of a Noetherian scheme has Noetherian
source. -/
public theorem isNoetherian {X Y : Scheme.{u}} [IsNoetherian X] {f : Y ⟶ X}
    (hf : SurfacePointBlowupChain X Y f) : IsNoetherian Y :=
  isNoetherian_of_pointBlowupChain hf.toPointBlowupChain

/-- A chain of blowups at two-dimensional closed points of a regular Noetherian scheme of
dimension two has source again regular of dimension two. One step is the global form of
[Stacks, Tag 0AGR]. -/
public theorem isRegular {X Y : Scheme.{u}} [IsNoetherian X] {f : Y ⟶ X}
    (hf : SurfacePointBlowupChain X Y f) (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) :
    AlgebraicGeometry.IsRegular Y ∧ topologicalKrullDim Y = 2 := by
  induction hf with
  | refl => exact ⟨hX, hdim⟩
  | step hh w hw _ ih =>
      have := hh.isNoetherian
      exact isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton _ ih.1 ih.2 w hw

/-- The inverse image of an effective Cartier divisor along a chain of blowups at two-dimensional
closed points is an effective Cartier divisor. -/
public theorem isEffectiveCartierDivisor_comap {X Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : SurfacePointBlowupChain X Y f) {D : X.IdealSheafData}
    (hD : IsEffectiveCartierDivisor D) : IsEffectiveCartierDivisor (D.comap f) :=
  hf.toPointBlowupChain.isEffectiveCartierDivisor_comap hD

end SurfacePointBlowupChain

/-! ### Principalization along a chain of blowups at two-dimensional points -/

/-- The inverse image along a chain of a product of an effective Cartier divisor with an ideal
sheaf whose inverse image is an effective Cartier divisor is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap_mul {X Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : SurfacePointBlowupChain X Y f) {A B : X.IdealSheafData}
    (hA : IsEffectiveCartierDivisor A) (hB : IsEffectiveCartierDivisor (B.comap f)) :
    IsEffectiveCartierDivisor ((A * B).comap f) := by
  rw [AlgebraicGeometry.comap_mul]
  exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
    (hf.isEffectiveCartierDivisor_comap hA) hB

/-- **The colength induction of [Stacks, Tag 0AHH], recording the centres.** Let `T` be a finite
set of closed points of a scheme `X` whose local rings are regular of dimension two, and let `I`
be a quasi-coherent sheaf of ideals whose quotient is supported on `T`. Then there is a sequence
of blowups at closed points with two-dimensional local rings along which `I` becomes an invertible
sheaf of ideals. Each step is the colength descent
`Stacks.ResolutionOfSurfaces.CartierDescent.pointBlowupColengthDescent`, the local splitting of
[Stacks, Tag 0AGT] globalised. -/
public theorem exists_surfacePointBlowupChain_isEffectiveCartierDivisor
    {X : Scheme.{u}} (T : Finset X)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (I : X.IdealSheafData) (hI : (I.support : Set X) ⊆ (T : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), SurfacePointBlowupChain X Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) := by
  suffices H : ∀ (m : ℕ∞) (X : Scheme.{u}) (T : Finset X),
      (∀ x ∈ T, IsClosed ({x} : Set X)) →
      (∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x)) →
      (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) →
      ∀ I : X.IdealSheafData, (I.support : Set X) ⊆ (T : Set X) →
      totalColength I T = m →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), SurfacePointBlowupChain X Y f ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) by
    exact H _ X T hclosed hregular hdim I hI rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro X T hclosed hregular hdim I hI hm
  by_cases hItop : I = ⊤
  · subst hItop
    refine ⟨X, 𝟙 X, .refl, ?_⟩
    rw [Scheme.IdealSheafData.comap_id]
    exact Stacks.Divisors.isEffectiveCartierDivisor_top
  · obtain ⟨x, hx⟩ : ((I.support : Set X)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      exact hItop ((Scheme.IdealSheafData.support_eq_bot_iff (I := I)).mp
        (TopologicalSpace.Closeds.coe_eq_empty.mp hemp))
    have hxT : x ∈ T := Finset.mem_coe.mp (hI hx)
    have hxclosed : IsClosed ({x} : Set X) := hclosed x hxT
    set M : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hxclosed⟩ with hM
    obtain ⟨d, S', J', hsplit, hS'closed, hS'reg, hS'dim, hJ'supp, -, hlt⟩ :=
      CartierDescent.pointBlowupColengthDescent X T I hclosed hregular hdim hI x hx hxclosed M hM
    obtain ⟨Y, g, hchain, hcartier⟩ :=
      ih (totalColength J' S') (hm ▸ hlt) (blowUp M) S' hS'closed hS'reg hS'dim J' hJ'supp rfl
    have hbase : SurfacePointBlowupChain X (blowUp M) (blowUpToBase M) := by
      simpa using (SurfacePointBlowupChain.refl (X := X)).step x hxclosed (hdim x hxT)
    refine ⟨Y, g ≫ blowUpToBase M, hbase.comp hchain, ?_⟩
    rw [Scheme.IdealSheafData.comap_comp, ← hsplit]
    exact isEffectiveCartierDivisor_comap_mul hchain
      (Stacks.Divisors.isEffectiveCartierDivisor_pow
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M) d) hcartier

/-- **[Stacks, Tag 0BIB] along a chain of blowups at two-dimensional points.** Let `X` be a
regular Noetherian scheme of dimension two and let `Z ⊆ X` be a closed subscheme containing no
irreducible component of `X`. Then there is a sequence of blowups at closed points with
two-dimensional local rings along which the inverse image of `Z` becomes an effective Cartier
divisor. -/
public theorem exists_surfacePointBlowupChain_comap_isEffectiveCartierDivisor
    (X : Scheme.{u}) [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), SurfacePointBlowupChain X Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  classical
  obtain ⟨D, Z', hD, hZ', hcover⟩ :=
    AlgebraicGeometry.exists_integral_effectiveCartierDivisors_cover X Z hZ (Or.inr hX)
  have hcover' : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ I : D, ((I.1 : X.IdealSheafData).support : Set X) := by
    simpa only [Set.iUnion_subtype] using hcover
  obtain ⟨a, hE, hZE, U, hU, hcodim⟩ :=
    AlgebraicGeometry.exists_effectiveCartierDivisor_agree_off_codimension_two X Z
      (fun I : D => (I.1 : X.IdealSheafData)) Z' (fun I => hD I.1 I.2) hZ' hcover'
  set E : X.IdealSheafData := a.prod fun I n => (I.1 : X.IdealSheafData) ^ n with hEdef
  have hpoints : ∀ x ∈ (Z.support : Set X) \ (U : Set X), IsClosed ({x} : Set X) :=
    fun x hx => isClosed_singleton_of_codimension_two hdim x (hcodim x hx.1 hx.2)
  have hfinite : ((Z.support : Set X) \ (U : Set X)).Finite :=
    finite_of_forall_isClosed_singleton
      (Z.support.isClosed.inter U.isOpen.isClosed_compl) hpoints
  obtain ⟨-, hstalk⟩ :
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    ((AlgebraicGeometry.isRegular_tfae X).out 1 2 (by simp) (by simp)).mp hX
  obtain ⟨Y, f, hchain, hQ⟩ :=
    exists_surfacePointBlowupChain_isEffectiveCartierDivisor hfinite.toFinset
      (fun x hx => hpoints x (hfinite.mem_toFinset.mp hx))
      (fun x _ => hstalk x)
      (fun x hx => by
        have hx' := hfinite.mem_toFinset.mp hx
        exact ringKrullDim_stalk_eq_two hdim x (hcodim x hx'.1 hx'.2))
      (cartierQuotient Z E)
      (by
        rw [hfinite.coe_toFinset]
        exact support_cartierQuotient_subset Z E U hU.symm)
  refine ⟨Y, f, hchain, ?_⟩
  rw [← mul_cartierQuotient_eq hE hZE]
  exact isEffectiveCartierDivisor_comap_mul hchain hE hQ

/-! ### Inheritance of resolvability -/

/-- The strict transform of a reduced closed subscheme under the blowup at a closed point is
reduced: away from the subscheme it is isomorphic to the subscheme, and at a point of the
subscheme it is the blowup of the subscheme there ([Stacks, Tag 080E]), which is reduced
([Stacks, Tag 0808]). -/
private theorem isReduced_subscheme_transformIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] (p : X) (hp : IsClosed ({p} : Set X)) :
    IsReduced (transformIdeal I p hp).subscheme := by
  by_cases hIp : p ∈ I.support
  · obtain ⟨y, rfl⟩ : ∃ y : I.subscheme, I.subschemeι y = p := ⟨⟨p, hIp⟩, rfl⟩
    have hy : IsClosed ({y} : Set I.subscheme) :=
      isClosed_singleton_of_subschemeι_eq I hp y rfl
    obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp I y hy hp
    exact isReduced_of_isOpenImmersion d.hom
  · obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self I p hp
      (transformToCurve_isIso_of_notMem_support I p hp hIp)
    exact isReduced_of_isOpenImmersion e.hom

/-- **One blowup at a two-dimensional closed point of a regular Noetherian surface.** If every
one-dimensional irreducible component of a closed subscheme `E` admits a chain of blowups at
closed points with regular source, then so does every one-dimensional irreducible component of the
inverse image of `E` under the blowup at a closed point with two-dimensional local ring. -/
private theorem resolvable_componentIdeal_comap_blowUp {W : Scheme.{u}} [IsNoetherian W]
    (hW : AlgebraicGeometry.IsRegular W) (hdimW : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) (hdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (E : W.IdealSheafData)
    (hE : ∀ C : irreducibleComponents E.subscheme,
      topologicalKrullDim (componentIdeal E C).subscheme = 1 →
      ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal E C).subscheme),
        PointBlowupChain (componentIdeal E C).subscheme Set.univ P g ∧
          AlgebraicGeometry.IsRegular P)
    (C : irreducibleComponents (E.comap (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).subscheme)
    (hC : topologicalKrullDim (componentIdeal (E.comap (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C).subscheme = 1) :
    ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal (E.comap (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C).subscheme),
      PointBlowupChain (componentIdeal (E.comap (blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C).subscheme
        Set.univ P g ∧ AlgebraicGeometry.IsRegular P := by
  obtain hmax | ⟨C', hC'⟩ :=
    isExceptionalFibreComponent_or_exists_eq_reducedStrictTransform w hw E C
  · have hreg := isRegular_subscheme_vanishingIdeal_of_isExceptionalFibreComponent w hw hW hdimW
      hdim _ hmax
    have hv : Scheme.IdealSheafData.vanishingIdeal
        (componentIdeal (E.comap (blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C).support =
        componentIdeal (E.comap (blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C := by
      rw [componentIdeal]
      exact congrArg Scheme.IdealSheafData.vanishingIdeal
        (Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _))
    rw [hv] at hreg
    exact ⟨_, 𝟙 _, .refl, hreg⟩
  · have hint : IsIntegral (componentIdeal E C').subscheme := isIntegral_componentIdeal E C'
    have := isReduced_subscheme_transformIdeal (componentIdeal E C') w hw
    have heq : componentIdeal (E.comap (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))) C =
        transformIdeal (componentIdeal E C') w hw := by
      rw [hC']
      exact reducedStrictTransform_eq_transformIdeal (componentIdeal E C') w hw
    rw [heq] at hC ⊢
    have hdimC' : topologicalKrullDim (componentIdeal E C').subscheme = 1 :=
      topologicalKrullDim_eq_one_of_transformIdeal (componentIdeal E C') w hw hC
    exact exists_pointBlowupChain_isRegular_transformIdeal (componentIdeal E C') hint hdimC'
      (hE C' hdimC') w hw

/-- **Inheritance of resolvability along a chain of blowups at two-dimensional points.** Let `X`
be a regular Noetherian scheme of dimension two and `E ⊆ X` a closed subscheme each of whose
one-dimensional irreducible components admits a chain of blowups at closed points with regular
source — condition (3) of [Stacks, Tag 0BI4]. Then along any chain of blowups of `X` at closed
points with two-dimensional local rings, every one-dimensional irreducible component of the
inverse image of `E` again admits such a chain.

A component of the inverse image under one blowup is either a component of the exceptional fibre,
which is regular (part (1) of [Stacks, Tag 0AGQ]), or the strict transform of a component of `E`,
to which the condition passes. -/
public theorem resolvable_componentIdeal_comap_of_surfacePointBlowupChain
    {X V : Scheme.{u}} [IsNoetherian X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X = 2) {f : V ⟶ X} (hf : SurfacePointBlowupChain X V f)
    (E : X.IdealSheafData)
    (hE : ∀ C : irreducibleComponents E.subscheme,
      topologicalKrullDim (Stacks.Divisors.componentIdeal E C).subscheme = 1 →
      ∃ (P : Scheme.{u}) (g : P ⟶ (Stacks.Divisors.componentIdeal E C).subscheme),
        PointBlowupChain (Stacks.Divisors.componentIdeal E C).subscheme Set.univ P g ∧
          AlgebraicGeometry.IsRegular P)
    (C : irreducibleComponents (E.comap f).subscheme)
    (hC : topologicalKrullDim (Stacks.Divisors.componentIdeal (E.comap f) C).subscheme = 1) :
    ∃ (P : Scheme.{u}) (g : P ⟶ (Stacks.Divisors.componentIdeal (E.comap f) C).subscheme),
      PointBlowupChain (Stacks.Divisors.componentIdeal (E.comap f) C).subscheme Set.univ P g ∧
        AlgebraicGeometry.IsRegular P := by
  suffices h : ∀ (V' : Scheme.{u}) (f' : V' ⟶ X), SurfacePointBlowupChain X V' f' →
      ∀ J : V'.IdealSheafData, J = E.comap f' →
        ∀ C' : irreducibleComponents J.subscheme,
          topologicalKrullDim (componentIdeal J C').subscheme = 1 →
          ∃ (P : Scheme.{u}) (g : P ⟶ (componentIdeal J C').subscheme),
            PointBlowupChain (componentIdeal J C').subscheme Set.univ P g ∧
              AlgebraicGeometry.IsRegular P from
    h V f hf _ rfl C hC
  intro V' f' hf'
  induction hf' with
  | refl =>
      intro J hJ C' hC'
      rw [Scheme.IdealSheafData.comap_id] at hJ
      subst hJ
      exact hE C' hC'
  | @step W h hh w hw hdimw ih =>
      intro J hJ
      rw [Scheme.IdealSheafData.comap_comp] at hJ
      subst hJ
      intro C' hC'
      have := hh.isNoetherian
      obtain ⟨hW, hdimW⟩ := hh.isRegular hX hdim
      exact resolvable_componentIdeal_comap_blowUp hW hdimW w hw hdimw (E.comap h)
        (ih _ rfl) C' hC'

end Stacks.ResolutionOfSurfaces

end
