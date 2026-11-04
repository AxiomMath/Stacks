module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosedVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedFibreTwoChartVanishing
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic

/-!
# Global étale cohomology vanishing from acyclicity on the affine opens

Let `X` be a quasi-compact quasi-separated scheme and let `F` be an abelian sheaf on its small
étale site. Assume

1. `F` is acyclic over every *affine* open of `X`: `H^n(V, F) = 0` for every affine open `V` and
   every `n > 0`; and
2. for a quasi-compact open `U` and an affine open `V`, every degree-zero section of `F` over
   `U ⊓ V` is the difference of a section over `U` and a section over `V`
   (`Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.SectionsSub`).

Then the global étale cohomology of `F` vanishes in every positive degree.

This is the Mayer--Vietoris descent from the affine opens of a quasi-compact quasi-separated
scheme to the scheme itself, in **every** degree. The degree `n ≥ 2` of the induction step is the
Mayer--Vietoris window `H^{n-1}(U ⊓ V) ⟶ H^n(U ⊔ V) ⟶ H^n(U) ⊞ H^n(V)` with both ends vanishing,
which is `Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_subsingleton` and
needs no hypothesis beyond (1); degree `1` is the one degree that window does not reach, the
window there exhibiting `H^1(U ⊔ V)` as a quotient of `H^0(U ⊓ V)`, and hypothesis (2) is exactly
what kills that quotient. The passage from the affine opens to `X` is the induction principle of
[Stacks, Tag 08DR], whose induction step is a quasi-compact open together with an affine one —
which is the shape the Mayer--Vietoris square has.

## Main results

* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_degreeOne_of_sectionsSub` —
  **the degree-one Mayer--Vietoris step.** Vanishing of `H^1` over `U` and over `V`, together
  with the degree-zero gluing condition for the pair, gives vanishing of `H^1` over `U ⊔ V`.
* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_acyclic_and_sectionsSub` —
  the induction step of [Stacks, Tag 08DR] for acyclicity in all positive degrees.
* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologyOpens_of_affineOpens_acyclic` —
  acyclicity over every quasi-compact open of a quasi-separated scheme.
* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic` — **the
  conclusion**: the global étale cohomology of a quasi-compact quasi-separated scheme vanishes in
  positive degrees.

## Why both hypotheses are needed

Hypothesis (1) alone does not suffice, and the counterexample is already visible in degree one:
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_two_opens` concludes only in degrees
`q ≥ 2` from acyclicity of two covering opens and their intersection, and its docstring records
that this is not an artefact. Hypothesis (2) is the degree-zero input the Čech argument supplies
in the applications: for a filtered colimit `F = colim f_i^{-1} G_i` of pullbacks of *injective*
abelian sheaves on the levels of an inverse system of schemes, a section over `U ⊓ V` comes from
a level, where the Mayer--Vietoris sequence of the injective sheaf `G_i` splits it as a
difference because `H^1(-, G_i)` vanishes identically.

## Implementation notes

Cohomology over an open subscheme is `Stacks.EtaleCohomology.StrictlyHenselian.opensCohomology`,
the restriction of `CategoryTheory.Sheaf.cohomologyPresheaf` along the inclusion of the opens of
`X` into the small étale site; it is the vocabulary both of the degree-one Mayer--Vietoris step
reused here and of `CategoryTheory.Sheaf.H'`, with which it agrees by unfolding. No comparison
with the étale cohomology of the open subscheme as a scheme in its own right is made or needed:
the whole induction runs over the objects `(opensToSite X).obj W` of the small étale site of `X`,
and only the last step — `⊤` being a terminal object — leaves them, through
`Stacks.EtaleCohomology.MayerVietoris.cohomologyTopIsoH`.

The site is `Stacks.EtaleCohomology.MayerVietoris.topology`, the single-universe presentation of
the small étale site of `X` that `CategoryTheory.Sheaf.H'` and the Mayer--Vietoris sequence of
[Stacks, Tag 0A50] are stated on.

## References

* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed (SectionsSub)
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)

universe u

namespace Stacks.EtaleCohomology.MayerVietoris

variable {X : Scheme.{u}} (F : Sheaf (topology X) AddCommGrpCat.{u + 1})

/-- **The degree-one Mayer--Vietoris step.** If the degree-one cohomology of `F` over `U` and
over `V` vanishes and every degree-zero section of `F` over `U ⊓ V` is a difference of sections
over `U` and over `V`, then the degree-one cohomology of `F` over `U ⊔ V` vanishes.

This is the one degree the window `H^{n₀}(U ⊓ V) ⟶ H^{n₁}(U ⊔ V) ⟶ H^{n₁}(U) ⊞ H^{n₁}(V)` of
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_subsingleton` does not reach:
there the source of the window is assumed to vanish, and in degree `n₁ = 1` it is `H^0(U ⊓ V)`,
which the acyclicity hypotheses do not constrain. The gluing condition replaces that assumption,
the connecting map killing every difference of sections. -/
theorem subsingleton_cohomologySup_degreeOne_of_sectionsSub (U V : X.Opens)
    (hsub : SectionsSub F U V)
    (hU : Subsingleton ((opensCohomology F 1).obj (op U)))
    (hV : Subsingleton ((opensCohomology F 1).obj (op V))) :
    Subsingleton ((opensCohomology F 1).obj (op (U ⊔ V))) := by
  have h : ∀ z : (opensCohomology F 1).obj (op (U ⊔ V)), z = 0 := fun z =>
    AbsolutelyIntegrallyClosed.eq_zero_of_mayerVietoris_degreeOne F le_sup_left le_sup_right
      rfl hsub z (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact ⟨fun x y => by rw [h x, h y]⟩

/-- **The induction step of [Stacks, Tag 08DR] for acyclicity.** If `F` is acyclic in positive
degrees over `U`, over `V` and over `U ⊓ V`, and if every degree-zero section over `U ⊓ V` is a
difference of sections over `U` and over `V`, then `F` is acyclic in positive degrees over
`U ⊔ V`.

Degree one is `subsingleton_cohomologySup_degreeOne_of_sectionsSub`; a degree `n₀ + 2` is the
Mayer--Vietoris window of
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_subsingleton`, whose source
`H^{n₀ + 1}(U ⊓ V)` is in a positive degree and therefore vanishes. -/
theorem subsingleton_cohomologySup_of_acyclic_and_sectionsSub (U V : X.Opens)
    (hsub : SectionsSub F U V)
    (hU : ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op U)))
    (hV : ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op V)))
    (hUV : ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op (U ⊓ V)))) :
    ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op (U ⊔ V))) := by
  intro n hn
  match n, hn with
  | 1, _ =>
    exact subsingleton_cohomologySup_degreeOne_of_sectionsSub F U V hsub (hU 1 one_pos)
      (hV 1 one_pos)
  | (n₀ + 2), _ =>
    exact subsingleton_cohomologySup_of_subsingleton F U V (n₀ + 1) (n₀ + 2) rfl
      (hUV (n₀ + 1) (by omega)) (hU (n₀ + 2) (by omega)) (hV (n₀ + 2) (by omega))

/-- **Acyclicity over every quasi-compact open from acyclicity over the affine opens.** Let `X`
be a quasi-separated scheme and let `F` be an abelian sheaf on its small étale site which is
acyclic in positive degrees over every affine open and which satisfies the degree-zero gluing
condition for every pair consisting of a quasi-compact open and an affine open. Then `F` is
acyclic in positive degrees over every quasi-compact open of `X`.

This is the induction principle of [Stacks, Tag 08DR] with the Mayer--Vietoris step
`subsingleton_cohomologySup_of_acyclic_and_sectionsSub`; the shape of that principle's induction
step — a quasi-compact open together with an affine one — is exactly the shape of the
Mayer--Vietoris square, which is what makes the two fit. -/
theorem subsingleton_cohomologyOpens_of_affineOpens_acyclic [QuasiSeparatedSpace X]
    (haff : ∀ V : X.Opens, IsAffineOpen V →
      ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op V)))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → SectionsSub F U V)
    (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op W)) :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (fun W => ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op W))) haff
    (fun U V hUc hVaff hPU hPV hPUV =>
      subsingleton_cohomologySup_of_acyclic_and_sectionsSub F U V
        (hsub U V hUc hVaff) hPU hPV hPUV)
    W hW

/-- **Global étale cohomology vanishing from acyclicity on the affine opens.** Let `X` be a
quasi-compact quasi-separated scheme and let `F` be an abelian sheaf on its small étale site.
If `F` is acyclic in positive degrees over every affine open of `X`, and if for every
quasi-compact open `U` and affine open `V` each degree-zero section of `F` over `U ⊓ V` is a
difference of sections over `U` and over `V`, then `H^q(X, F) = 0` for every `q > 0`.

The acyclicity over `⊤` is `subsingleton_cohomologyOpens_of_affineOpens_acyclic`, and `⊤` is a
terminal object of the small étale site of `X`, so cohomology over it is the global cohomology
`CategoryTheory.Sheaf.H` (`Stacks.EtaleCohomology.MayerVietoris.cohomologyTopIsoH`). -/
theorem subsingleton_H_of_affineOpens_acyclic [CompactSpace X] [QuasiSeparatedSpace X]
    (haff : ∀ V : X.Opens, IsAffineOpen V →
      ∀ n, 0 < n → Subsingleton ((opensCohomology F n).obj (op V)))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → SectionsSub F U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} F q) := by
  have : Subsingleton ((opensCohomology F q).obj (op (⊤ : X.Opens))) :=
    subsingleton_cohomologyOpens_of_affineOpens_acyclic F haff hsub ⊤
      (by simpa using isCompact_univ (X := X)) q hq
  exact AddCommGrpCat.subsingleton_of_isZero
    (Limits.IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton
      (G := F.H' q ((opensToSite X).obj ⊤)))
      (cohomologyTopIsoH X F q).symm)

end Stacks.EtaleCohomology.MayerVietoris

end
