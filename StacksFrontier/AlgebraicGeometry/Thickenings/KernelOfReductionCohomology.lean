module

public import StacksFrontier.CategoryTheory.Sites.SheafCohomology.ShortExactVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheafAffineVanishing
public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpacesCoefficientUniverse
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ChangeOfUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import StacksFrontier.Homology.DerivedLinear

/-!
# The cohomology of the kernel of reduction of `Gₐ`

Let `S` be a scheme of a big fppf site, `z : Z → S` a morphism of the site and `X → S` an object
of the big fppf site of `S` such that `X₀ = X ×_S Z → X` is a closed immersion. On the big fppf
site of `X`, restriction along the first projections `T ×_S Z → T` is a morphism
`Gₐ → Gₐ'`, where `Gₐ'(T) = Γ(T ×_S Z, 𝒪)`; let `ℱ` be its kernel, so that
`ℱ(T) = Ker(Γ(T, 𝒪_T) → Γ(T ×_S Z, 𝒪))`. If `X` is Noetherian of dimension `≤ 1`, then
`H^q(X, ℱⁿ) = 0` for every `q ≥ 2` and every `n`.

The proof:

* `Gₐ → Gₐ'` is an epimorphism of sheaves, and surjective on sections over every `T` with affine
  underlying scheme: `T ×_S Z → T` is a base change of the closed immersion `X₀ → X`, and a
  closed immersion into an affine scheme is surjective on global functions;
* `Gₐ` and `Gₐ'` are restrictions of `Gₐ` on the big fppf site of `S` along functors preserving
  affineness, so their positive-degree cohomology vanishes over objects with affine underlying
  scheme (`AlgebraicGeometry.BigFppfOver.isZero_H'_sheafPushforwardContinuous_of_isAffine`);
* the long exact sequence of `0 → ℱ → Gₐ → Gₐ' → 0` then kills the positive-degree cohomology of
  `ℱ`, hence of `ℱⁿ`, over every affine open of `X`;
* a sheaf with this vanishing has the cohomology of its restriction to the small Zariski site of
  `X` (`Stacks.Adequate.BigSite.zariskiSheafHEquiv`), which vanishes above the dimension of the
  Noetherian space `X` by Grothendieck's vanishing theorem.

## Main results

* `AlgebraicGeometry.BigFppfOver.isClosedImmersion_baseChangeFst_overMap`: `T ×_S Z → T` is a
  closed immersion for every `T` over `X`.
* `AlgebraicGeometry.BigFppfOver.epi_toBaseChangePushforward_overMap`: `Gₐ → Gₐ'` is an
  epimorphism of sheaves on the big fppf site of `X`.
* `AlgebraicGeometry.BigFppfOver.subsingleton_H'_of_affineOpenAcyclicity`: Grothendieck
  vanishing for an abelian sheaf on the big fppf site of a Noetherian scheme acyclic on its affine
  opens.
* `AlgebraicGeometry.BigFppfOver.affineOpenAcyclicity_of_isLimit_fan_kernel`: `ℱⁿ` is acyclic on
  the affine opens of `X`.
* `AlgebraicGeometry.BigFppfOver.subsingleton_H'_of_isLimit_fan_kernel_additiveGroupSheaf`:
  `H^q(X, ℱⁿ) = 0` for `q ≥ 2`.

## Implementation notes

The kernel `ℱ` and the product `ℱⁿ` are given as limit cones, not as `kernel` and `∏ᶜ`, which
are expensive to elaborate in these sheaf categories.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w u

namespace AlgebraicGeometry.BigFppfOver

attribute [local instance] hasSheafify_topology_over

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Z : Scheme.{u}} (hZ : B.Contains Z) (z : B.obj hZ ⟶ B.obj hS)

/-! ### The reduction map `Gₐ → Gₐ'` -/

/-- **`T ×_S Z → T` is a closed immersion for every `T` over `X`** as soon as `X ×_S Z → X` is
one: it is the base change of `X ×_S Z → X` along `T → X`. -/
theorem isClosedImmersion_baseChangeFst_overMap (U : BigFppfOver B S hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z U).left)) (T : Over U.left) :
    IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z ((Over.map U.hom).obj T)).left) := by
  have sq := (IsPullback.of_bot' (IsPullback.of_hasPullback (T.hom ≫ U.hom) z)
    (IsPullback.of_hasPullback U.hom z)).map B.inclusion
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip hi

/-- **`T ×_S Z` is affine for every affine `T` over `X`** as soon as `X ×_S Z → X` is a closed
immersion. -/
theorem isAffine_baseChange_overMap_of_isAffine (U : BigFppfOver B S hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z U).left)) (T : Over U.left)
    (hT : IsAffine (B.inclusion.obj T.left)) :
    IsAffine (B.inclusion.obj ((Over.map z).obj ((Over.pullback z).obj
      ((Over.map U.hom).obj T))).left) :=
  have := isClosedImmersion_baseChangeFst_overMap B hS hZ z U hi T
  have : IsAffine (B.inclusion.obj ((Over.map U.hom).obj T).left) := hT
  isAffine_of_isAffineHom (B.inclusion.map (Sheaf.baseChangeFst z ((Over.map U.hom).obj T)).left)

/-- **`Γ(T, 𝒪) → Γ(T ×_S Z, 𝒪)` is surjective for every affine `T` over `X`**, a closed immersion
into an affine scheme being surjective on global functions. -/
theorem surjective_toBaseChangePushforward_app_overMap (U : BigFppfOver B S hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z U).left)) (T : Over U.left)
    (hT : IsAffine (B.inclusion.obj T.left)) :
    Function.Surjective (((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z).hom.app
      (op ((Over.map U.hom).obj T))) := by
  have := isClosedImmersion_baseChangeFst_overMap B hS hZ z U hi T
  have : IsAffine (B.inclusion.obj ((Over.map U.hom).obj T).left) := hT
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (B.inclusion.map (Sheaf.baseChangeFst z ((Over.map U.hom).obj T)).left)).2

/-- **`Gₐ → Gₐ'` is an epimorphism of sheaves on the big fppf site of `X`.** It is surjective on
sections over every object with affine underlying scheme, and those objects cover every object
of the site. -/
theorem epi_toBaseChangePushforward_overMap (U : BigFppfOver B S hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z U).left)) :
    Epi (((Over.map U.hom).sheafPushforwardContinuous AddCommGrpCat.{u}
      (B.topology.over U.left) (BigFppfOver.topology B S hS)).map
        ((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z)) := by
  have : Sheaf.IsLocallySurjective (((Over.map U.hom).sheafPushforwardContinuous
      AddCommGrpCat.{u} (B.topology.over U.left) (BigFppfOver.topology B S hS)).map
        ((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z)) := by
    constructor
    intro V s
    have : (BigAffineFppf.inclusion B (B.inclusion.obj U.left) U.left.2).IsCoverDense
        (BigFppfOver.topology B (B.inclusion.obj U.left) U.left.2) :=
      Functor.IsDenseSubsite.isCoverDense
        (BigAffineFppf.topology B (B.inclusion.obj U.left) U.left.2) _ _
    refine (B.topology.over U.left).superset_covering ?_
      (Functor.IsCoverDense.is_cover
        (G := BigAffineFppf.inclusion B (B.inclusion.obj U.left) U.left.2)
        (K := BigFppfOver.topology B (B.inclusion.obj U.left) U.left.2) V)
    rintro W g ⟨c⟩
    rw [← c.fac]
    apply Sieve.downward_closed
    exact surjective_toBaseChangePushforward_app_overMap B hS hZ z U hi _ c.obj.property _
  infer_instance

/-! ### Grothendieck vanishing for sheaves acyclic on affine opens -/

open Stacks.CohomologyVanishing in
/-- **Grothendieck vanishing on a chosen big site of a Noetherian scheme.** Let `S₀` be a scheme
whose underlying space is Noetherian of dimension `≤ d`, and let `𝒫` be an abelian sheaf on a
chosen big `τ`-site over `S₀` whose positive-degree cohomology vanishes over every affine open of
`S₀`. Then `H^q((Sch/S₀)_τ, 𝒫) = 0` for every `q > d`.

The cohomology of `𝒫` is that of its restriction to the small Zariski site of `S₀`
(`Stacks.Adequate.BigSite.zariskiSheafHEquiv`), and the latter vanishes in degrees above the
dimension of the Noetherian space `S₀` (Grothendieck's vanishing theorem, [Stacks, Tag 02UZ], in
the form `subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le_of_coefficients` of the
namespace `Stacks.CohomologyVanishing`). -/
theorem _root_.Stacks.Adequate.BigSite.subsingleton_sheafH_of_affineOpenAcyclicity
    {τ : CoveringTopology} {S₀ : Scheme.{u}} (B' : Stacks.Adequate.BigSite τ S₀)
    [TopologicalSpace.NoetherianSpace S₀] {d : ℕ} (hdim : topologicalKrullDim S₀ ≤ d)
    [hZar : HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥S₀)
      AddCommGrpCat.{u})]
    [hBig : HasExt.{u} (Sheaf B'.topology AddCommGrpCat.{u})]
    (P : Sheaf B'.topology AddCommGrpCat.{u}) (hP : B'.AffineOpenAcyclicity P)
    (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H.{u} P q) := by
  have h1 : Subsingleton (Sheaf.H.{u} (B'.zariskiRestriction.obj P) q) :=
    subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le_of_coefficients.{u, u, u} hdim hq _
  exact (B'.zariskiSheafHEquiv.{u} P hP q).symm.toEquiv.subsingleton

/-- **Grothendieck vanishing on the big fppf site of a Noetherian scheme.** Let `X` be a scheme of
a big fppf site, Noetherian of dimension `≤ d`, and let `𝒫` be an abelian sheaf on the big fppf
site of `X` whose positive-degree cohomology vanishes over every affine open of `X`. Then
`H^q(X, 𝒫) = 0` for every `q > d`, in every `Ext` universe.

This is `Stacks.Adequate.BigSite.subsingleton_sheafH_of_affineOpenAcyclicity` for the chosen big
site `Stacks.Adequate.BigSite.ofBigFppfSite`, read at the final object `X` of the site
(`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'`) and moved to the
`Ext` universe `w` (`CategoryTheory.Abelian.Ext.chgUnivAddEquiv`). -/
theorem subsingleton_H'_of_affineOpenAcyclicity {X : Scheme.{u}} (hX : B.Contains X)
    [IsNoetherian X] {d : ℕ} (hdim : topologicalKrullDim X ≤ d)
    [HasExt.{w} (Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})]
    (P : Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})
    (hP : (Stacks.Adequate.BigSite.ofBigFppfSite B X hX).AffineOpenAcyclicity P)
    (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H' P q (Over.mk (𝟙 (B.obj hX)))) := by
  let hu : HasExt.{u} (Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite _
  have h2 : Subsingleton (Sheaf.H.{u} P q) :=
    Stacks.Adequate.BigSite.subsingleton_sheafH_of_affineOpenAcyclicity
      (Stacks.Adequate.BigSite.ofBigFppfSite B X hX) hdim
      (hZar := Stacks.Topology.hasExt_sheafOpens.{u, u} _) (hBig := hu) P hP q hq
  have h3 : Subsingleton (Sheaf.H'.{u} P q (Over.mk (𝟙 (B.obj hX)))) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'.{u} _ P q _
      Over.mkIdTerminal).1 h2
  exact @Equiv.subsingleton _ _ (@Ext.chgUnivAddEquiv.{w, u} _ _ _ _ hu _ _ _).toEquiv h3

/-! ### The kernel of reduction -/

section Kernel

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **The kernel of reduction and its finite powers are acyclic on the affine opens of `X`.**
Let `ℱ` be the kernel of `Gₐ → Gₐ'` on the big fppf site of `X`, where `X ×_S Z → X` is a closed
immersion, and `𝒫 = ℱⁿ`. Then the positive-degree cohomology of `𝒫` vanishes over every affine
open of `X`.

Over an object `T` of the site with affine underlying scheme, `Gₐ` and `Gₐ'` have no
positive-degree cohomology
(`AlgebraicGeometry.BigFppfOver.isZero_H'_sheafPushforwardContinuous_of_isAffine`, along
`Over.map f` and along `Over.map f ⋙ Over.pullback z ⋙ Over.map z`), and `Gₐ(T) → Gₐ'(T)` is
surjective; the long exact sequence of `0 → ℱ → Gₐ → Gₐ' → 0`
(`Stacks.Cohomology.LongExactSequence.isZero_H'_X₁_of_shortExact`) then kills the
positive-degree cohomology of `ℱ` over `T`, and that of `ℱⁿ` with it
(`CategoryTheory.Functor.isZero_obj_of_isLimit_fan`). -/
theorem affineOpenAcyclicity_of_isLimit_fan_kernel {X : Scheme.{u}} (hX : B.Contains X)
    (f : B.obj hX ⟶ B.obj hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z (Over.mk f)).left))
    (F : Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})
    (ι : F ⟶ ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS)).obj
        (BigFppfOver.additiveGroupSheaf S B hS))
    (w : ι ≫ ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS)).map
        ((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z) = 0)
    (hF : IsLimit (KernelFork.ofι ι w))
    {n : ℕ} (P : Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})
    (π : Fin n → (P ⟶ F)) (hP : IsLimit (Fan.mk P π)) :
    (Stacks.Adequate.BigSite.ofBigFppfSite B X hX).AffineOpenAcyclicity P := by
  let SC : ShortComplex (Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u}) :=
    ShortComplex.mk ι _ w
  have : Mono SC.f := mono_of_isLimit_fork hF
  have : Epi SC.g := epi_toBaseChangePushforward_overMap B hS hZ z (Over.mk f) hi
  have hSC : SC.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel SC hF }
  have : (Over.pullback z ⋙ Over.map z).IsContinuous (B.topology.over (B.obj hS))
      (B.topology.over (B.obj hS)) :=
    Functor.isContinuous_comp _ _ _ (B.topology.over (B.obj hZ)) _
  have : (Over.map f ⋙ Over.pullback z ⋙ Over.map z).IsContinuous
      (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS) :=
    Functor.isContinuous_comp _ _ _ (B.topology.over (B.obj hS)) _
  have hFT (T : Over (B.obj hX)) (hT : IsAffine (B.inclusion.obj T.left)) (q : ℕ) (hq : 0 < q) :
      IsZero (Sheaf.H' F q T) :=
    Stacks.Cohomology.LongExactSequence.isZero_H'_X₁_of_shortExact SC hSC T
      (isZero_H'_sheafPushforwardContinuous_of_isAffine B hS (B.obj hX) _
        (isZero_H'_additiveGroupSheaf_of_isAffine B hS) (Over.map f) (fun _ hW => hW) T hT)
      (isZero_H'_sheafPushforwardContinuous_of_isAffine B hS (B.obj hX) _
        (isZero_H'_additiveGroupSheaf_of_isAffine B hS) (Over.map f ⋙ Over.pullback z ⋙ Over.map z)
        (fun W hW => isAffine_baseChange_overMap_of_isAffine B hS hZ z (Over.mk f) hi W hW) T hT)
      (surjective_toBaseChangePushforward_app_overMap B hS hZ z (Over.mk f) hi T hT) q hq
  intro V hV q hq
  let T : Over (B.obj hX) := (Stacks.Adequate.BigSite.ofBigFppfSite B X hX).opensToBig.obj V
  have hT : IsAffine (B.inclusion.obj T.left) := hV
  have := Stacks.DerivedLinear.rightDerived_additive
    ((sheafSections (BigFppfOver.topology B X hX) AddCommGrpCat.{u}).obj (op T)) q
  exact Functor.isZero_obj_of_isLimit_fan
    (((sheafSections (BigFppfOver.topology B X hX) AddCommGrpCat.{u}).obj (op T)).rightDerived q)
    π hP ((hFT T hT q hq).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections _ F q T).symm)

end Kernel

/-- **`H^q(X, ℱⁿ) = 0` for `q ≥ 2`.** Let `S` be a scheme of a big fppf site, `z : Z → S` and
`f : X → S` morphisms of the site with `X ×_S Z → X` a closed immersion, and `X` Noetherian of
dimension `≤ 1`. On the big fppf site of `X` let `ℱ` be the kernel of the restriction
`Gₐ → Gₐ'` along the first projections `T ×_S Z → T`, so `ℱ(T) = Ker(Γ(T, 𝒪) → Γ(T ×_S Z, 𝒪))`,
and let `𝒫 = ℱⁿ`. Then `H^q(X, 𝒫) = 0` for every `q ≥ 2`.

This is the step of the proof of [Stacks, Tag 0AFB] in which the kernel of the reduction of a
smooth group scheme, a finite power of the kernel of reduction of `Gₐ`, is shown to have no
second cohomology over the curve. -/
theorem subsingleton_H'_of_isLimit_fan_kernel_additiveGroupSheaf {X : Scheme.{u}}
    (hX : B.Contains X) (f : B.obj hX ⟶ B.obj hS)
    (hi : IsClosedImmersion (B.inclusion.map (Sheaf.baseChangeFst z (Over.mk f)).left))
    [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})]
    (F : Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})
    (ι : F ⟶ ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS)).obj
        (BigFppfOver.additiveGroupSheaf S B hS))
    (w : ι ≫ ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS)).map
        ((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z) = 0)
    (hF : IsLimit (KernelFork.ofι ι w))
    {n : ℕ} (P : Sheaf (BigFppfOver.topology B X hX) AddCommGrpCat.{u})
    (π : Fin n → (P ⟶ F)) (hP : IsLimit (Fan.mk P π)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H' P q (Over.mk (𝟙 (B.obj hX)))) :=
  subsingleton_H'_of_affineOpenAcyclicity B hX (d := 1) (by exact_mod_cast hdim) P
    (affineOpenAcyclicity_of_isLimit_fan_kernel B hS hZ z hX f hi F ι w hF P π hP) q (by omega)

end AlgebraicGeometry.BigFppfOver

end
