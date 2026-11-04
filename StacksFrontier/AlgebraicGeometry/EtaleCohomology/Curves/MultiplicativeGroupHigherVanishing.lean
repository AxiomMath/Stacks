module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageMultiplicative
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOneVanishing

/-!
# Higher vanishing for the multiplicative group on a smooth curve

Let `X` be a smooth curve over an algebraically closed field `k`, let `η = Spec k(X)` be its
generic point and `j : η ⟶ X` the inclusion of the generic point. Two vanishing statements of
the source are proved here.

**Stacks 03RK**: `H^p_étale(X, j_* 𝐆_{m,η}) = 0` for every `p ≥ 1`, with no hypothesis beyond the
source's. The source deduces this from
the Leray spectral sequence `E₂^{p,q} = H^p(X, R^q j_* 𝐆_{m,η})`, whose `q ≥ 1` rows vanish by
Stacks 03RJ and whose abutment `H^{p+q}(η, 𝐆_m)` vanishes for `p + q ≥ 1` by Stacks 03RG. Here
the same deduction is made without a spectral sequence, through the edge isomorphism in the one
case in which it is an isomorphism for elementary reasons: if `R^q j_* 𝐆_{m,η} = 0` for `q ≥ 1`
then `j_*` applied to an injective resolution of `𝐆_{m,η}` is an injective resolution of
`j_* 𝐆_{m,η}`, so `H^p(X, j_* 𝐆_{m,η})` is the cohomology of `Γ(X, j_* I^•) = Γ(η, I^•)`, which
is `H^p(η, 𝐆_m)`. The collapse is
`Stacks.RightDerivedComp.objIso` and the identification of the composite
`Γ(X, -) ∘ j_*` with `Γ(η, -)` is
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompGlobalSectionsIso`.

**Stacks 03RM**: `H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`. This is the long exact sequence of
étale cohomology attached to the divisor sequence of Stacks 03RI,

`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0`:

the segment `H^{q-1}(X, ⨁_x i_{x,*} 𝐙) → H^q(X, 𝐆_{m,X}) → H^q(X, j_* 𝐆_{m,η})` has both outer
groups zero, the left one by Stacks 03RL since `q - 1 ≥ 1`, the right one by Stacks 03RK.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImageCompGlobalSectionsIso`: global sections on
  `X_étale` composed with the direct image along `i : Y ⟶ X` are global sections on `Y_étale`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived`:
  the edge argument on an integral scheme, from the vanishing of `R^q j_* 𝐆_{m,η}` and of
  `H^q(η, 𝐆_m)` in positive degree.
* `Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf`:
  **Stacks 03RK**.
* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`:
  **Stacks 03RM**.

## Implementation notes

**The inputs of Stacks 03RK.** Both are proved in the library and used here.

* Stacks 03RJ, that `R^q j_* 𝐆_{m,η} = 0` for `q ≥ 1`, is
  `Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one`,
  at the transcendence-degree-one function field of a curve
  (`AlgebraicGeometry.trdeg_functionField_eq_one`). Neither input uses smoothness, so Stacks 03RK
  is stated for a curve.
* Stacks 03RG, that `H^q_étale(Spec k(X), 𝐆_m) = 0` for `q ≥ 1`, is
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_functionField`, Stacks 03RG
  at the function field of a curve.

**The carried hypotheses of the Stacks 03RM statement here, and the tags they are.** The
statement of Stacks 03RM in this file carries the inputs `h03RJ` (Stacks 03RJ) and `h03RG`
(Stacks 03RG) as hypotheses, together with the following.

* `d`, `hzero` and `hSE`, that `0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_x i_{x,*} 𝐙 → 0` is a short exact
  sequence of abelian sheaves on `X_étale`: this is **Stacks 03RI**, the fundamental exact
  sequence. The library has that sequence only read on sections over an irreducible étale
  `X`-scheme, in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections`, where
  exactness on the left and the complex property are proved; passing from there to a short exact
  sequence of sheaves needs the decomposition of a general étale `X`-scheme into irreducible
  pieces and the local principality of a divisor on a nonsingular curve, neither of which is
  present. The first map is not carried: it is the comparison morphism
  `Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along `j`, which the library
  already has.

Nothing else is assumed. The hypotheses on `X` are exactly those of the source — a smooth curve
over an algebraically closed field — and each degree range is the source's, quantified over the
degree.

**Why the degree range of Stacks 03RM is `q ≥ 2` and not `q ≥ 1`.** In the long exact sequence
the group to the left of `H^q(X, 𝐆_{m,X})` is `H^{q-1}(X, ⨁_x i_{x,*} 𝐙)`, which Stacks 03RL
kills only for `q - 1 ≥ 1`. In degree one that group is `Div(X)`, which does not vanish, and
indeed `H^1(X, 𝐆_m) = Pic(X)`.

**Quasi-compactness and quasi-separatedness.** Stacks 03RL is stated for a quasi-compact,
quasi-separated scheme locally of finite type over the field. A curve supplies all three: it is
a variety, so its structure morphism is quasi-compact, separated and locally of finite type, and
the base `Spec k` is affine, so `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`
and `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` transfer the two topological
conditions to `X`. They are supplied inside the proof, not assumed.

**Why the composite of global sections with the direct image is global sections.** Global
sections on the small étale site are the right adjoint of the constant sheaf functor,
`CategoryTheory.Sheaf.Γ`, and on a site with a terminal object they are the sections over it,
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`. The direct image is restriction along base change,
so its composite with sections over a terminal object `T` of `X_étale` is, on the nose, sections
over `T ×_X Y`; and that object is terminal in `Y_étale` by
`Stacks.EtaleCohomology.isTerminalSmallEtaleBaseChangeObj`. The middle step of
`etaleAbelianDirectImageCompGlobalSectionsIso` is therefore an identity, and only the two outer
steps are comparisons.

**Coefficients and pinned universes.** Abelian sheaves are taken with coefficients in
`AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, which is the universe at which Stacks 03RL is
available, and cohomology is `CategoryTheory.Sheaf.H.{u + 1, u + 1}`. Three instances have to be
recorded with their coefficient universe pinned, because the general statements are indexed by
`max (u + 1) v` and instance search cannot solve `max (u + 1) ?v = u + 1`: the Grothendieck
abelian structure (as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology`), which is what
makes `HasExt.{u + 1}` available; additivity of global sections; and preservation of injective
objects by the direct image, which exists in the tree for
`Stacks.EtaleCohomology.smallEtalePushforwardAb` — the same functor, under a name that instance
search does not unfold.

## References

* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK): the vanishing for
  `j_* 𝐆_{m,η}`, proved here.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the theorem, proved
  here.
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG): used from the library
  for Stacks 03RK.
* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ): used from the library
  for Stacks 03RK.
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): carried as the
  hypotheses `d`, `hzero` and `hSE`.
* [Stacks Project, Tag 03RL](https://stacks.math.columbia.edu/tag/03RL): used from the library.
* [Stacks Project, Tag 03QC](https://stacks.math.columbia.edu/tag/03QC): the Leray spectral
  sequence, which the source uses and which the collapse argument here replaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Pinned instances at the coefficient universe `u + 1` -/

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Global sections of abelian sheaves on the small étale site of `X : Scheme.{u}` with
coefficients in `AddCommGrpCat.{u + 1}` are additive. This is
`Stacks.Cohomology.GlobalSections.additive_Γ` with its coefficient universe pinned. -/
local instance additive_globalSections_smallEtale_pinned (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} X.smallEtaleTopology

/-- The direct image along `i : Y ⟶ X` on abelian sheaves of the small étale sites, with
coefficients in `AddCommGrpCat.{u + 1}`, preserves injective objects. This is
`Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects`, which is about the
same functor under a name instance search does not unfold. -/
local instance preservesInjectiveObjects_etaleAbelianDirectImage_pinned {X Y : Scheme.{u}}
    (i : Y ⟶ X) : (etaleAbelianDirectImage.{u, u + 1} i).PreservesInjectiveObjects :=
  smallEtalePushforwardAb_preservesInjectiveObjects i

/-! ### Global sections of a direct image -/

/-- **Global sections on `X_étale` composed with the direct image along `i : Y ⟶ X` are global
sections on `Y_étale`.** The direct image is restriction along base change, so its composite
with sections over a terminal object `T` of `X_étale` is, on the nose, sections over the base
change `T ×_X Y`, which is a terminal object of `Y_étale`. -/
def etaleAbelianDirectImageCompGlobalSectionsIso {X Y : Scheme.{u}} (i : Y ⟶ X) :
    etaleAbelianDirectImage.{u, u + 1} i ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{u + 1} (terminalIsTerminal (C := X.Etale))) ≪≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminalSmallEtaleBaseChangeObj i (terminalIsTerminal (C := X.Etale)))).symm

/-! ### Stacks 03RK: the cohomology of `j_* 𝐆_{m,η}` -/

/-- **The edge argument for the direct image of `𝐆_m` along the generic point.** Let `X` be an
integral scheme, let `η = Spec k(X)` be its generic point and `j : η ⟶ X` the inclusion. If the
higher direct images `R^q j_* 𝐆_{m,η}` vanish for `q ≥ 1` and the étale cohomology of `η` with
coefficients in `𝐆_m` vanishes in positive degree, then

`H^p_étale(X, j_* 𝐆_{m,η}) = 0` for every `p ≥ 1`.

This is the edge isomorphism of the Leray spectral sequence obtained directly: the first
hypothesis makes `j_*` applied to an injective resolution of `𝐆_{m,η}` an injective resolution
of `j_* 𝐆_{m,η}` (`Stacks.RightDerivedComp.objIso`, which needs `j_*` to be additive, left exact
and to preserve injective objects — all three hold, `j_*` being the right adjoint of an exact
functor), and `Γ(X, -) ∘ j_*` is `Γ(η, -)`
(`Stacks.EtaleCohomology.etaleAbelianDirectImageCompGlobalSectionsIso`). So
`H^p(X, j_* 𝐆_{m,η}) ≅ H^p(η, 𝐆_m)`, which the second hypothesis kills. -/
theorem subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived
    {X : Scheme.{u}} [IsIntegral X]
    (hR : ∀ q : ℕ, 0 < q →
      IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))))
    (hH : ∀ q : ℕ, 1 ≤ q → Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)) q))
    (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((genericPointDirectImage.{u, u + 1} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) p) := by
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    X.smallEtaleTopology _ p]
  refine IsZero.of_iso ?_ (Stacks.RightDerivedComp.objIso
    (etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X))
    (InjectiveResolution.of (Stacks.Kummer.multiplicativeSheaf.{u, u + 1}
      (Spec X.functionField))) hR
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) p).symm
  refine IsZero.of_iso ?_ ((ModuleSheafCohomology.rightDerivedIso
    (etaleAbelianDirectImageCompGlobalSectionsIso (genericPointInclusion X)) p).app _)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    (Spec X.functionField).smallEtaleTopology _ p).1 (hH p hp)

/-- **Stacks Project, Tag 03RK.** Let `X` be a curve over an algebraically closed field `k`,
with structure morphism `g`, let `η = Spec k(X)` be its generic point and `j : η ⟶ X` the
inclusion of the generic point. Then

`H^p_étale(X, j_* 𝐆_{m,η}) = 0` for every `p ≥ 1`.

The source assumes `X` smooth; the proof does not use smoothness, so it is not assumed and the
statement is more general than the tag. The smooth case, with the source's hypotheses verbatim,
is `Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_smoothCurve`.

The source argues by the Leray spectral sequence `E₂^{p,q} = H^p(X, R^q j_* 𝐆_{m,η})`, whose
`q ≥ 1` rows vanish by Stacks 03RJ and whose abutment `H^{p+q}(η, 𝐆_m)` vanishes for
`p + q ≥ 1` by Stacks 03RG. The proof here is the edge isomorphism of that spectral sequence,
`Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived`,
with both inputs proved: Stacks 03RJ is
`Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one`,
whose premise is `AlgebraicGeometry.trdeg_functionField_eq_one`, and Stacks 03RG at the function
field of `X` is `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_functionField`. -/
@[stacks 03RK "vanishing of the positive-degree étale cohomology of the direct image of 𝐆_m
along the generic point of a curve over an algebraically closed field"]
theorem subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((genericPointDirectImage.{u, u + 1} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) p) := by
  letI := functionFieldAlgebra k g
  exact subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived
    (isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one k
      (trdeg_functionField_eq_one k g))
    (subsingleton_sheafH_multiplicativeSheaf_spec_functionField k g) p hp

/-! ### Stacks 03RM: the cohomology of `𝐆_m` on a smooth curve -/

/-- **Stacks Project, Tag 03RM.** Let `X` be a smooth curve over an algebraically closed field
`k`, let `η = Spec k(X)` be its generic point and `j : η ⟶ X` the inclusion of the generic
point. Then

`H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`.

The proof is the long exact sequence of étale cohomology attached to the divisor sequence
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0` of Stacks 03RI: the segment
`H^{q-1}(X, ⨁_x i_{x,*} 𝐙) → H^q(X, 𝐆_{m,X}) → H^q(X, j_* 𝐆_{m,η})` has both outer groups
zero, the left one by Stacks 03RL since `q - 1 ≥ 1`, the right one by Stacks 03RK.

Stacks 03RL is used from the library, as
`Stacks.EtaleCohomology.subsingleton_sheafH_sigma_closedPointPushforward_smallEtale`, and
the vanishing of `H^q(X, j_* 𝐆_{m,η})` is the edge argument
`Stacks.EtaleCohomology.subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived`
(which is how Stacks 03RK is proved above), applied to the hypotheses `h03RJ` (Stacks 03RJ) and
`h03RG` (Stacks 03RG) carried here. The
divisor sequence itself is carried as its second map `d` with `hzero` and `hSE` (Stacks 03RI);
its first map is the comparison morphism
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along `j`, which restricts an
invertible global function on an étale `X`-scheme `U` to the generic fibre `U ×_X η`. -/
@[stacks 03RM "vanishing of the degree ≥ 2 étale cohomology of 𝐆_m on a smooth curve over an
algebraically closed field, over Tag 03RI, Tag 03RJ and Tag 03RG as hypotheses"]
theorem subsingleton_sheafH_multiplicativeSheaf_smoothCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (d : (genericPointDirectImage.{u, u + 1} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)) ⟶
        closedPointDivisorSheaf.{u, u + 1} X)
    (hzero : multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X) ≫ d = 0)
    (hSE : (ShortComplex.mk
      (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X)) d
      hzero).ShortExact)
    (h03RJ : ∀ q : ℕ, 0 < q →
      IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))))
    (h03RG : ∀ q : ℕ, 1 ≤ q → Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)) q))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  exact Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact hSE p (p + 1) rfl
    (subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_of_isZero_rightDerived
      h03RJ h03RG (p + 1) (by lia))
    (subsingleton_sheafH_sigma_closedPointPushforward_smallEtale g p (by lia))

end Stacks.EtaleCohomology

end
