module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AdditiveSheafAssociatedStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.Frobenius

/-!
# The Artin–Schreier sequence as a datum, and [Stacks, Tag 0A3K] with nothing carried

The vanishing theorems of [Stacks, Tag 0A3K] in
`ArtinSchreierSequence/ConstantCoefficientVanishing.lean` are stated against
`Stacks.ArtinSchreier.ArtinSchreierSequence`, a structure holding a short exact sequence
`0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` of abelian sheaves on the small étale site, and against `hcomp`, a
transfer of vanishing from the cohomology of the structure sheaf to the étale cohomology of `𝐆_a`.
This file supplies both.

The sequence is built for every scheme on which the prime `p` vanishes out of
`Stacks.ArtinSchreier.constantArtinSchreierSequence_shortExact` — [Stacks, Tag 0A3J], proved in
`ArtinSchreierSequence/ConstantKernel.lean`. Its middle and right terms are
`Stacks.ArtinSchreier.additiveSheaf`, the sheaf of global functions on the small étale site; the
left map is the sheafified inclusion of the scalar functions `Stacks.ArtinSchreier.zmodSheafHom`,
and the right map is `Stacks.ArtinSchreier.artinSchreierMap`, `x ↦ x ^ p - x`.

The transfer is `Stacks.ArtinSchreier.subsingleton_sheafH_additiveSheaf_of_isZero_hgroup`, the
composite of three comparisons: `𝐆_a` is the associated sheaf of the structure module,
[Stacks, Tag 03P6] (`AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf`, at
coefficients `AddCommGrpCat.{u}`); the étale cohomology of that associated sheaf is the Zariski
cohomology of the structure sheaf in positive degrees, [Stacks, Tag 03P2]
(`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup`); and raising
the coefficient universe from `u` to `u + 1` does not change étale cohomology
(`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`), the lift of `𝐆_a` at `u` being `𝐆_a` at
`u + 1` (`AlgebraicGeometry.additiveSheafBaseUliftIso`).

## Main definitions

* `Stacks.ArtinSchreier.constantArtinSchreierSequenceDatum`: the Artin–Schreier sequence of a
  scheme of characteristic `p`, as an `ArtinSchreierSequence` term.

## Main results

* `Stacks.ArtinSchreier.subsingleton_sheafH_additiveSheaf_of_isZero_hgroup`: vanishing of the
  cohomology of the structure sheaf in a positive degree gives vanishing of the étale cohomology
  of `𝐆_a` in that degree.
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAffine_constantSequence`:
  **[Stacks, Tag 0A3K] (1)**, with nothing carried.
* `subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_constantSequence`:
  **[Stacks, Tag 0A3K] (2)**, with nothing carried.

## Implementation notes

The coefficient universe is `u + 1`: `ArtinSchreierSequence p S` holds its sheaves in
`AddCommGrpCat.{u + 1}`, whereas `ConstantKernel.lean` is polymorphic in a second universe `v` and
works in `AddCommGrpCat.{max (u + 1) v}`; the two agree at `v := u + 1`, where the left term of
the sequence *is* `Stacks.ArtinSchreier.etaleConstantZMod S p`.

The characteristic hypothesis is `(p : Γ(S, ⊤)) = 0`. For a scheme over a ring of
characteristic `p`, `Stacks.ArtinSchreier.natCast_eq_zero_of_charP` derives it.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the sequence.
* [Stacks Project, Tag 0A3K](https://stacks.math.columbia.edu/tag/0A3K)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2): the comparison.
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6): `𝐆_a` is the associated
  sheaf of the structure module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.ArtinSchreier

/-- A scheme over a commutative ring of characteristic `p` has `p` vanishing in its ring of
global functions: the structure morphism carries `(p : k) = 0` along. -/
public theorem natCast_eq_zero_of_charP (k : Type u) [CommRing k] (p : ℕ) [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : (p : Γ(X, ⊤)) = 0 :=
  Stacks.Frobenius.isInCharacteristic_of_over (p := p) (Over.mk f)

/-- **The Artin–Schreier sequence of a scheme of characteristic `p`**, as an
`Stacks.ArtinSchreier.ArtinSchreierSequence` term. The middle and right terms are `𝐆_a`, the
sheaf of global functions on the small étale site; the inclusion of `𝐙/p𝐙` is the sheafification
of the map sending a residue class to the corresponding scalar function, the second map is
`x ↦ x ^ p - x`, and short exactness is [Stacks, Tag 0A3J],
`Stacks.ArtinSchreier.constantArtinSchreierSequence_shortExact`.

The coefficient universe of `ConstantKernel.lean` is instantiated at `v := u + 1`, where its
left term is `Stacks.ArtinSchreier.etaleConstantZMod X p`. -/
@[sga "1 XI 6.7", sga "4 IX 3.5"]
public noncomputable def constantArtinSchreierSequenceDatum (X : Scheme.{u}) {p : ℕ}
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) : ArtinSchreierSequence p X where
  natCast_eq_zero := hX
  Ga := additiveSheaf.{u, u + 1} X
  ι := zmodSheafHom.{u, u + 1} X hX
  φ := artinSchreierMap.{u, u + 1} X hp hX
  comp_eq_zero := zmodSheafHom_comp_artinSchreierMap.{u, u + 1} X hp hX
  shortExact := constantArtinSchreierSequence_shortExact.{u, u + 1} X hp hX

/-- The middle and right terms of the supplied Artin–Schreier sequence are `𝐆_a`. -/
@[simp]
public theorem constantArtinSchreierSequenceDatum_Ga (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    (constantArtinSchreierSequenceDatum X hp hX).Ga = additiveSheaf.{u, u + 1} X :=
  rfl

/-- The left map of the supplied Artin–Schreier sequence is the inclusion of the scalar
functions. -/
@[simp]
public theorem constantArtinSchreierSequenceDatum_ι (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    (constantArtinSchreierSequenceDatum X hp hX).ι = zmodSheafHom.{u, u + 1} X hX :=
  rfl

/-- The right map of the supplied Artin–Schreier sequence is `x ↦ x ^ p - x`. -/
@[simp]
public theorem constantArtinSchreierSequenceDatum_φ (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    (constantArtinSchreierSequenceDatum X hp hX).φ = artinSchreierMap.{u, u + 1} X hp hX :=
  rfl

/-- **The comparison of [Stacks, Tag 03P2] in the shape the Artin–Schreier argument uses.** On
any scheme `S`, if the cohomology of the structure sheaf vanishes in a positive degree `i`, then
so does the étale cohomology of `𝐆_a` at coefficients `AddCommGrpCat.{u + 1}`, in every `Ext`
universe.

`𝐆_a` at `u + 1` is the coefficient lift of `𝐆_a` at `u`
(`AlgebraicGeometry.additiveSheafBaseUliftIso`), whose cohomology is that of the lift
(`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`); `𝐆_a` at `u` is the associated sheaf of the
structure module ([Stacks, Tag 03P6],
`AlgebraicGeometry.additiveSheafBaseIsoSmallEtaleAssociatedSheaf`), whose positive-degree étale
cohomology vanishes with that of the structure sheaf by
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup`. -/
public theorem subsingleton_sheafH_additiveSheaf_of_isZero_hgroup (S : Scheme.{u})
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : ℕ) (hi : 0 < i)
    (h : IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf))) :
    Subsingleton (Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} S) i) := by
  have : IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology S AddCommGrpCat.{u}
  let : HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse S
  let hE : HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  have h0 : Subsingleton (Sheaf.H.{u, u} (smallEtaleAssociatedSheaf S (Scheme.unitModule S)) i) :=
    subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup S (Scheme.unitModule S) i hi h
  have h1 : Subsingleton (Sheaf.H.{u, u} (additiveSheafBase S) i) :=
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
      (additiveSheafBaseIsoSmallEtaleAssociatedSheaf S) i).injective.subsingleton
  have h2 : Subsingleton (Sheaf.H.{u + 1, u + 1} ((sheafCompose S.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (additiveSheafBase S)) i) :=
    (smallEtaleSheafHUliftAddEquiv S (additiveSheafBase S) i).symm.injective.subsingleton
  have h3 : Subsingleton (Sheaf.H.{u + 1, u + 1} (additiveSheaf.{u, u + 1} S) i) :=
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
      (additiveSheafBaseUliftIso S).symm i).injective.subsingleton
  let e : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} S) i ≃
      Sheaf.H.{u + 1, u + 1} (additiveSheaf.{u, u + 1} S) i := Abelian.Ext.chgUniv
  exact e.injective.subsingleton

/-- `hcomp` of the Artin–Schreier argument, in the shape the vanishing theorems of
`ConstantCoefficientVanishing.lean` take it, from a vanishing range starting above `n`: only
degrees above `n` are ever fed to it there. -/
private theorem hcomp_of_lt (S : Scheme.{u})
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ)
    (hvan : ∀ i : ℕ, n < i →
      IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf)))
    (i : ℕ) (hi : n < i) :
    Subsingleton (Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} S) i) :=
  subsingleton_sheafH_additiveSheaf_of_isZero_hgroup S i (by omega) (hvan i hi)

/-- **The Artin–Schreier degree shift, with nothing carried.** Let `S` be a scheme on which the
prime `p` vanishes. If the cohomology of the structure sheaf of `S` vanishes in all degrees above
`n`, then the étale cohomology of `𝐙/p𝐙` vanishes in all degrees at least `n + 2`. -/
public theorem subsingleton_etaleH_constantZMod_of_hgroup_vanishing_constantSequence (p : ℕ)
    [Fact p.Prime] (S : Scheme.{u}) (hS : (p : Γ(S, ⊤)) = 0)
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ)
    (hvan : ∀ i : ℕ, n < i →
      IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf)))
    (q : ℕ) (hq : n + 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  exact subsingleton_sheafH_X₁_of_shortExact
    (constantArtinSchreierSequenceDatum S Fact.out hS).shortExact q' (q' + 1) rfl
    (hcomp_of_lt S n hvan q' (by omega)) (hcomp_of_lt S n hvan (q' + 1) (by omega))

/-- **[Stacks, Tag 0A3K] (1).** Let `p` be a prime and let `S` be an affine scheme on which `p`
vanishes. Then `H ^ q (S_étale, 𝐙/p𝐙) = 0` for every `q ≥ 2`.

The cohomology of the structure sheaf of an affine scheme vanishes in positive degree by
[Stacks, Tag 01XB], so the Artin–Schreier degree shift applies with `n = 0`. -/
@[stacks 0A3K "part (1)"]
public theorem subsingleton_etaleH_constantZMod_of_isAffine_constantSequence (p : ℕ)
    [Fact p.Prime] (S : Scheme.{u}) [IsAffine S] (hS : (p : Γ(S, ⊤)) = 0)
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) :=
  subsingleton_etaleH_constantZMod_of_hgroup_vanishing_constantSequence p S hS 0
    (fun i hi => Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen S
      (SheafOfModules.unit S.ringCatSheaf) ⊤ (isAffineOpen_top S) i hi)
    q hq

/-- **[Stacks, Tag 0A3K] (2).** Let `p` be a prime and let `S` be a quasi-compact and
quasi-separated scheme on which `p` vanishes and of dimension at most `d`. Then
`H ^ q (S_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 2`.

The underlying space of `S` is spectral, so the cohomology of the structure sheaf vanishes above
its dimension by [Stacks, Tag 0A3G], and the Artin–Schreier degree shift applies with `n = d`. -/
@[stacks 0A3K "part (2)", sga "4½ Arcata 4.4" "H^q(X_0, special case"]
public theorem subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_constantSequence
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : (p : Γ(S, ⊤)) = 0)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (S : Type u)) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ) (hdim : topologicalKrullDim (S : Type u) ≤ (d : WithBot ℕ∞))
    (q : ℕ) (hq : d + 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) :=
  subsingleton_etaleH_constantZMod_of_hgroup_vanishing_constantSequence p S hS d
    (fun i hi => Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology
      (SheafOfModules.unit S.ringCatSheaf) i (by omega)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d (S : Type u)
        inferInstance inferInstance
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj (SheafOfModules.unit S.ringCatSheaf))
        i hdim hi))
    q hq

end Stacks.ArtinSchreier

end
