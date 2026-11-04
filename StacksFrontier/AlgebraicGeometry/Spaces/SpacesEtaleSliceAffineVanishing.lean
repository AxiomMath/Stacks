module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentToSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineObjectVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyOverObjectVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DenseSubsiteGlobalVanishing
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.SurjectiveFromFirstVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct

/-!
# Serre vanishing on the slices of the spaces-étale site

Let `X` be an algebraic space over a scheme `S`, let `C = X_{spaces, étale}` be its ringed
spaces-étale site, let `V` be an object of `C` and let `F` be a quasi-coherent module on the slice
`C/V`.  For an object `T` of `C/V` whose underlying algebraic space is affine, the cohomology of
`F` over `T` vanishes in positive degrees.  This is the vanishing that condition (3) of the
unbounded cohomological descent of Stacks 0DC1 asks of the family of quasi-coherent modules,
with the bound `d_V = 0`, as Stacks 0DC5 asserts; the source deduces it from Stacks 01XB and the
discussion of Stacks 071Y.

The iterated slice `(C/V)/T` is the spaces-étale site of the algebraic space `Y` underlying `T`
(`AlgebraicGeometry.Space.SpacesEtale.iteratedSliceEquivSmall`).  Reindexing the restriction of
`F` along that equivalence gives a quasi-coherent module on the ringed spaces-étale site of the
affine algebraic space `Y`, whose positive-degree cohomology vanishes by
`AlgebraicGeometry.Space.SmallEtale.subsingleton_sheafH_quasicoherent`; the vanishing is carried
back along the equivalence by
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_sheafCongr_inverse`, and from the
global cohomology of the slice to the module cohomology over `T` by
`Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH_over`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.ringOver`: the structure sheaf of the slice `C/V`.
* `AlgebraicGeometry.Space.SpacesEtale.iteratedSliceEquivSmall`: `(C/V)/T` is the spaces-étale
  site of the algebraic space underlying `T`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.subsingleton_sheafH_over_of_isQuasicoherentOnSite`: the
  abelian cohomology of the restriction to `(C/V)/T` vanishes in positive degrees.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_moduleCohomology_of_isAffineSpace`: **the module
  cohomology of `F` over `T` vanishes in positive degrees.**

## References

* [Stacks Project, Tag 0DC5](https://stacks.math.columbia.edu/tag/0DC5)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 071Y](https://stacks.math.columbia.edu/tag/071Y)
* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The structure sheaf of the slice of the ringed spaces-étale site of `X` at `V`. -/
abbrev ringOver (V : SpacesEtale B S hS X) :
    Sheaf ((topology B S hS X).over V) RingCat.{u + 1} :=
  (ringSheaf (spacesEtaleRingedSite B S hS X).O).over V

variable {B S hS X}

/-- The iterated slice `(C/V)/T` of the spaces-étale site of `X` is the spaces-étale site of the
algebraic space underlying `T`. -/
abbrev iteratedSliceEquivSmall {V : SpacesEtale B S hS X} (T : Over V) :
    Over T ≌ SpacesEtale B S hS T.left.obj.left :=
  T.iteratedSliceEquiv.trans (sliceEquivSmall B S hS T.left)

/-- The inverse of `iteratedSliceEquivSmall` is a dense subsite inclusion: it is the composite of
the two dense subsite inclusions inverse to `Over.iteratedSliceEquiv` and to
`AlgebraicGeometry.Space.SpacesEtale.sliceEquivSmall`. -/
instance isDenseSubsite_iteratedSliceEquivSmall_inverse {V : SpacesEtale B S hS X} (T : Over V) :
    (iteratedSliceEquivSmall T).inverse.IsDenseSubsite (topology B S hS T.left.obj.left)
      (((topology B S hS X).over V).over T) :=
  have : T.iteratedSliceEquiv.inverse.IsDenseSubsite ((topology B S hS X).over T.left)
      (((topology B S hS X).over V).over T) := inferInstance
  Functor.isDenseSubsite_comp _ ((topology B S hS X).over T.left) _ _ _

/-- Vanishing of the cohomology of a module over `A` in the slice `C₀/A` follows from that of its
transport along an equivalence `C₀/A ≌ D` of sites that is a dense subsite inclusion in both
directions. -/
private theorem subsingleton_sheafH_over_of_equivalence {C₀ : Type (u + 1)} [Category.{u + 1} C₀]
    {J₀ : GrothendieckTopology C₀} {R : Sheaf J₀ RingCat.{u + 1}} (M : SheafOfModules.{u + 1} R)
    (A : C₀) {D : Type (u + 1)} [Category.{u + 1} D] (K : GrothendieckTopology D)
    (e : Over A ≌ D) [e.functor.IsContinuous (J₀.over A) K] [e.inverse.IsContinuous K (J₀.over A)]
    [e.inverse.IsDenseSubsite K (J₀.over A)] [HasSheafify K AddCommGrpCat.{u + 1}]
    [HasSheafify (J₀.over A) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (J₀.over A) AddCommGrpCat.{u + 1})]
    {S : Sheaf K RingCat.{u + 1}}
    (φ : S ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K (J₀.over A)).obj (R.over A))
    (q : ℕ)
    (hvan : Subsingleton (Sheaf.H.{u + 1}
      ((SheafOfModules.toSheaf.{u + 1} S).obj ((SheafOfModules.pushforward.{u + 1} φ).obj
        (M.over A))) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      (((SheafOfModules.toSheaf.{u + 1} R).obj M).over A) q) := by
  have hTD : IsTerminal (e.functor.obj (Over.mk (𝟙 A))) :=
    IsTerminal.isTerminalObj e.functor _ Over.mkIdTerminal
  have h2 := Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_sheafCongr_inverse
    (J₀.over A) K e Over.mkIdTerminal hTD _ q hvan
  let G := (SheafOfModules.toSheaf.{u + 1} (R.over A)).obj (M.over A)
  let E := e.sheafCongr (J₀.over A) K AddCommGrpCat.{u + 1}
  let i₁ := Stacks.SheafOfModules.toSheafPushforwardIso φ (M.over A)
  let i₂ : G ≅ ((SheafOfModules.toSheaf.{u + 1} R).obj M).over A :=
    Stacks.SheafOfModules.toSheafPushforwardIso (𝟙 (R.over A)) M
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    (E.inverse.mapIso i₁ ≪≫ (E.unitIso.app G).symm ≪≫ i₂) q h2

/-- **Serre vanishing on an iterated slice of the spaces-étale site.**  For a quasi-coherent module
`F` on `C/V` and an object `T` of `C/V` with affine underlying algebraic space, the global
cohomology of the restriction of the underlying abelian sheaf of `F` to `(C/V)/T` vanishes in
positive degrees. -/
theorem subsingleton_sheafH_over_of_isQuasicoherentOnSite (V : SpacesEtale B S hS X)
    (F : SheafOfModules.{u + 1} (ringOver B S hS X V)) (hF : F.IsQuasicoherentOnSite)
    (T : Over V) (hT : IsAffineSpace B S hS T.left.obj.left.1) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      (((SheafOfModules.toSheaf.{u + 1} (ringOver B S hS X V)).obj F).over T) q) := by
  let e := iteratedSliceEquivSmall T
  let J := ((topology B S hS X).over V).over T
  let K := topology B S hS T.left.obj.left
  have hinv : e.inverse.IsDenseSubsite K J := isDenseSubsite_iteratedSliceEquivSmall_inverse T
  have : e.symm.functor.IsContinuous K J :=
    Functor.IsDenseSubsite.instIsContinuous K J e.inverse
  have : e.functor.IsDenseSubsite J K := inferInstance
  have : e.symm.inverse.IsDenseSubsite J K := inferInstanceAs (e.functor.IsDenseSubsite J K)
  have : e.functor.IsContinuous J K := Functor.IsDenseSubsite.instIsContinuous J K e.functor
  have : e.inverse.IsContinuous K J := Functor.IsDenseSubsite.instIsContinuous K J e.inverse
  have hFT : (F.over T).IsQuasicoherentOnSite := Stacks.SheafOfModules.isQuasicoherent_over F hF T
  let N : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS T.left.obj.left).O) :=
    (SheafOfModules.pushforward.{u + 1}
      (𝟙 (Stacks.SheafOfModules.reindexRing K e.symm ((ringOver B S hS X V).over T)))).obj
        (F.over T)
  have hN : N.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_reindex e.symm _ (F.over T)
  have hvan := SmallEtale.subsingleton_sheafH_quasicoherent B S hS T.left.obj.left N hT hN q hq
  exact subsingleton_sheafH_over_of_equivalence F T K e
    (𝟙 (Stacks.SheafOfModules.reindexRing K e.symm ((ringOver B S hS X V).over T))) q hvan

/-- **Serre vanishing over an affine object of a slice of the spaces-étale site.**  For a
quasi-coherent module `F` on the slice `C/V` of the ringed spaces-étale site and an object `T` of
`C/V` with affine underlying algebraic space, `H^p(T, F) = 0` for every `p > 0`.

The three sheafification and injectivity hypotheses are implicit so that they unify with those
of the goal rather than being synthesised; they are all propositions. -/
theorem isZero_moduleCohomology_of_isAffineSpace (V : SpacesEtale B S hS X)
    {_ : HasSheafify ((topology B S hS X).over V) AddCommGrpCat.{u + 1}}
    {_ : ((topology B S hS X).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}}
    {_ : EnoughInjectives (SheafOfModules.{u + 1} (ringOver B S hS X V))}
    (F : SheafOfModules.{u + 1} (ringOver B S hS X V)) (hF : F.IsQuasicoherentOnSite)
    (T : Over V) (hT : IsAffineSpace B S hS T.left.obj.left.1) (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.Cohomology.moduleCohomology (ringOver B S hS X V) T p F) :=
  Stacks.Cohomology.isZero_moduleCohomology_of_subsingleton_sheafH_over _ T p F
    (subsingleton_sheafH_over_of_isQuasicoherentOnSite V F hF T hT p hp)

/-- **Serre vanishing over an affine object of the spaces-étale site.**  For a quasi-coherent
module `M` on the ringed spaces-étale site of `X` and an object `Q` of it with affine underlying
algebraic space, the global cohomology of the restriction of the underlying abelian sheaf of `M`
to the slice at `Q` vanishes in positive degrees. -/
theorem subsingleton_sheafH_over_of_isQuasicoherentOnSite_site
    (M : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS X).O))
    (hM : M.IsQuasicoherentOnSite) (Q : SpacesEtale B S hS X)
    (hQ : IsAffineSpace B S hS Q.obj.left.1) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      (((SheafOfModules.toSheaf.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS X).O)).obj
        M).over Q) q) := by
  let e := sliceEquivSmall B S hS Q
  let K := topology B S hS Q.obj.left
  let N := moduleToSmall B S hS X Q M
  have hN : N.IsQuasicoherentOnSite := isQuasicoherentOnSite_moduleToSmall B S hS X Q M hM
  have hvan := SmallEtale.subsingleton_sheafH_quasicoherent B S hS Q.obj.left N hQ hN q hq
  exact subsingleton_sheafH_over_of_equivalence M Q K e
    (𝟙 (Stacks.SheafOfModules.reindexRing K e.symm
      ((ringSheaf (spacesEtaleRingedSite B S hS X).O).over Q))) q hvan

/-- **Sections of a short exact sequence of modules on the spaces-étale site are surjective
over an affine object** when the kernel is quasi-coherent: the first cohomology of the kernel
over the object vanishes. -/
theorem surjective_val_app_of_shortExact_of_isAffineSpace
    {T : ShortComplex (SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS X).O))}
    (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (Q : SpacesEtale B S hS X)
    (hQ : IsAffineSpace B S hS Q.obj.left.1) :
    Function.Surjective (T.g.val.app (Opposite.op Q)) := by
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) Q
  have : ((topology B S hS X).overPullback AddCommGrpCat.{u + 1} Q).IsRightAdjoint :=
    (extensionByZeroAdjunction B S hS X Q).isRightAdjoint
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) Q
  refine Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH' _ _ hT Q ?_
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ?_
  exact (Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'.{u + 1}
    (topology B S hS X) Q
    (extensionByZeroAdjunction B S hS X Q) _ 1).1
    (subsingleton_sheafH_over_of_isQuasicoherentOnSite_site T.X₁ h₁ Q hQ 1 Nat.one_pos)

end AlgebraicGeometry.Space.SpacesEtale
