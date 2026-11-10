module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.NodeBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDescentAtWorstNodal
public import StacksFrontier.AlgebraicGeometry.Curves.NodeExtensionFixesBranches
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationFibreResidue
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# Vector fields on an at-worst-nodal curve and on its normalization

This file states and proves Tag 0E68: for `k` algebraically closed and `X` a one-dimensional
proper `k`-scheme with at worst nodal singularities and normalization `ν : X^ν ⟶ X`,
```
Der_k(𝒪_X, 𝒪_X) = {D' ∈ Der_k(𝒪_{X^ν}, 𝒪_{X^ν}) | D' fixes every x^ν ∈ S},
```
where `S` is the set of points of `X^ν` at which `ν` is not an isomorphism; these are the points
above the nodes of `X`. The equality is read through `ν^♯`, which is injective on sections
(`Stacks.Curves.app_normalization_injective`): a vector field `D` on `X` is identified with the
vector field `D'` on `X^ν` for which `D' (ν^♯ s) = ν^♯ (D s)`, and the two inclusions say that
this identification is defined on all of the left-hand side and lands exactly on the right-hand
side.

The two inclusions are already available:

* `⊆` is `Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities` — a
  vector field on `X` extends uniquely to one on `X^ν`.
* `⊇` is `Stacks.Curves.existsUnique_descend_normalization_of_hasAtWorstNodalSingularities` — a
  vector field on `X^ν` fixing the points over the nodes descends uniquely to one on `X`.

What makes them an *equality* rather than two one-way constructions is that the extension
produced by the first lands in the right-hand side, i.e. that it fixes the points over the
nodes. That is the source's remark that, `𝒪_{X^ν, x'}` being `k + (u)`, the extension "fixes
`x'`"; it is `Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode`, and
`Stacks.Curves.stalkDerivation_algebraMap_eq_of_extension` is what feeds the sheaf-level
extension into it — the derivation induced on `(ν_* 𝒪_{X^ν})_x` by the extension restricts on
`𝒪_{X, x}` to the derivation induced there by the vector field on `X`.

## Generality

`Stacks.Curves.derivations_eq_normalization_derivations_fixing_nodes` proves the equality without
properness or connectedness: it asks only that `X` be reduced, that its quasi-compact opens have
finitely many irreducible components, which is what the construction of the normalization needs,
and that its diagonal be affine, which is what the gluing of the extension over the preimages of
two affine opens needs. `Stacks.Curves.NodalVectorFields.range_branchPair` states the tag for a
proper `X`, deriving those three properties.

In `Stacks.Curves.derivations_eq_normalization_derivations_fixing_nodes` the condition that a
vector field on `X^ν` "fix every `x^ν ∈ S`" is stated on stalks: at every node `x` of `X`, the
derivation induced on `(ν_* 𝒪_{X^ν})_x` fixes every `k`-point of that stalk. For `ν` finite and
`k` algebraically closed this is the condition of Section 53.26 at every closed point of `X^ν`
above `x`: `Stacks.Curves.forall_fixes_stalkDerivation_of_forall_fixes` passes from the points to
the stalk, through the closed point that the kernel of a `k`-point cuts out over an affine open,
and `Stacks.Curves.fixes_of_forall_fixes_stalkDerivation` back, through the residue at a point
and `Stacks.Curves.SheafDerivationOf.fixes_of_isAffineOpen`, which reduces fixing a point to one
affine neighbourhood of it. `Stacks.Curves.NodalVectorFields.range_branchPair` is stated with the
source's condition.

## Main results

* `Stacks.Curves.stalkDerivation_algebraMap_eq_of_extension` — the derivation induced on a stalk
  of `ν_* 𝒪_{X^ν}` by an extension of a vector field restricts to the one induced by the vector
  field itself.
* `Stacks.Curves.not_exists_isIso_normalization_restrict_iff` — the points where the
  normalization is not an isomorphism are the points above the nodes.
* `Stacks.Curves.SheafDerivationOf.fixes_of_isAffineOpen` — fixing a point is decided on one
  affine neighbourhood.
* `Stacks.Curves.forall_fixes_stalkDerivation_of_forall_fixes` and
  `Stacks.Curves.fixes_of_forall_fixes_stalkDerivation` — fixing the points of a fibre and
  fixing the `k`-points of the stalk of the direct image are the same condition.
* `Stacks.Curves.existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities` — the
  unique extension of a vector field on `X` fixes the points over every node.
* `Stacks.Curves.derivations_eq_normalization_derivations_fixing_nodes` — the equality without
  properness.
* `Stacks.Curves.NodalVectorFields.range_branchPair` — **Tag 0E68.**

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.Curves

section Bridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **An extension of a vector field restricts, on each stalk, to the vector field.** Let
`ν : Y ⟶ X` be a morphism over `Spec k`, let `D` be a vector field on `X` and `D'` one on `Y`
with `D' (ν^♯ s) = ν^♯ (D s)` for every local section `s` of `𝒪_X`. Then the `k`-derivation that
`D'` induces on `(ν_* 𝒪_Y)_x` sends the image of a germ `a ∈ 𝒪_{X, x}` to the image of
`D a`.

Both sides are computed on a representative: the image in `(ν_* 𝒪_Y)_x` of the germ of `s` is
the germ of `ν^♯ s`, by the naturality of the germ with respect to `ν^♯`, and the two induced
derivations send germs to germs of values (`Stacks.Curves.stalkDerivation_germ`,
`Stacks.Curves.ownStalkDerivation_germ`). -/
theorem stalkDerivation_algebraMap_eq_of_extension (ν : Y ⟶ X) (hX : X ⟶ Spec (.of k))
    (D : SheafDerivationOf hX) (D' : SheafDerivationOf (ν ≫ hX))
    (hcompat : ∀ (U : X.Opens) (s : Γ(X, U)),
      D'.onSections ((ν.app U).hom s) = (ν.app U).hom (D.onSections s))
    (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
    letI := directImageStalkAlgebra ν x
    letI := directImageStalkFieldAlgebra ν hX x
    ∀ a : X.presheaf.stalk x,
      stalkDerivation ν D' x
          (algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x) a) =
        algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)
          (ownStalkDerivation D x a) := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
  let := directImageStalkAlgebra ν x
  let := directImageStalkFieldAlgebra ν hX x
  intro a
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have hg : ∀ t : Γ(X, U), (ν.base _* Y.presheaf).germ U x hx ((ν.app U).hom t) =
      algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)
        ((X.presheaf.germ U x hx).hom t) := fun t =>
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ν.c t).symm
  rw [← hg s, stalkDerivation_germ, hcompat U s, hg (D.onSections s),
    ownStalkDerivation_germ D U hx s]

end Bridge

section Fixing

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **Fixing a point is decided on one affine neighbourhood.** Let `D` be a vector field on `Y`,
let `y` be a closed point and let `O` be an affine open containing `y`. If every section of `𝒪_Y`
over `O` vanishing at `y` is carried by `D` to a section vanishing at `y`, then `D` fixes `y`.

A section `s` over another affine open `V ∋ y` is compared with `O` on a basic open
`W = D(f) ⊆ V ∩ O` of `O` containing `y`: there `s = a / fⁿ` with `a` a section over `O`, so
`a` vanishes at `y`, hence so does `D a`, and the Leibniz rule applied to `s fⁿ = a` in the
local ring at `y`, where `f` is a unit, shows that `D s` vanishes at `y`. -/
theorem SheafDerivationOf.fixes_of_isAffineOpen {g : Y ⟶ Spec (.of k)} (D : SheafDerivationOf g)
    (y : Y) (hy : IsClosed ({y} : Set Y)) {O : Y.Opens} (hO : IsAffineOpen O) (hyO : y ∈ O)
    (h : ∀ s : Γ(Y, O), y ∉ Y.basicOpen s → y ∉ Y.basicOpen (D.onSections s)) :
    D.Fixes y hy := by
  rw [D.fixes_iff_basicOpen]
  intro V s hs hDs
  have hyV : y ∈ (V : Y.Opens) := Y.basicOpen_le _ hDs
  obtain ⟨f, hfV, hyf⟩ := hO.exists_basicOpen_le (V := (V : Y.Opens)) ⟨y, hyV⟩ hyO
  have hWO : Y.basicOpen f ≤ O := Y.basicOpen_le f
  have := hO.isLocalization_basicOpen f
  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj (Submonoid.powers f)
    ((Y.presheaf.map (homOfLE hfV).op).hom s)
  obtain ⟨n, hn⟩ := m.2
  change (Y.presheaf.map (homOfLE hfV).op).hom s * (Y.presheaf.map (homOfLE hWO).op).hom m =
    (Y.presheaf.map (homOfLE hWO).op).hom a at ham
  set M := IsLocalRing.maximalIdeal (Y.presheaf.stalk y)
  have hmem : ∀ {U : Y.Opens} (hyU : y ∈ U) (t : Γ(Y, U)),
      y ∉ Y.basicOpen t ↔ Y.presheaf.germ U y hyU t ∈ M := fun hyU t => by
    rw [Scheme.mem_basicOpen Y t y hyU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hgerm : ∀ {U : Y.Opens} (hle : Y.basicOpen f ≤ U) (t : Γ(Y, U)),
      Y.presheaf.germ (Y.basicOpen f) y hyf ((Y.presheaf.map (homOfLE hle).op).hom t) =
        Y.presheaf.germ U y (hle hyf) t := fun hle t =>
    Y.presheaf.germ_res_apply (homOfLE hle) y hyf t
  have hunit : IsUnit (Y.presheaf.germ O y hyO m) := by
    rw [← hn, map_pow]
    exact ((Scheme.mem_basicOpen Y f y hyO).mp hyf).pow n
  have h1 := congrArg (Y.presheaf.germ (Y.basicOpen f) y hyf) ham
  simp only [map_mul, hgerm] at h1
  have hsM : Y.presheaf.germ V y hyV s ∈ M := (hmem hyV s).mp hs
  have haM : Y.presheaf.germ O y hyO a ∈ M := by
    rw [← h1]
    exact M.mul_mem_right _ hsM
  have hDaM := (hmem hyO _).mp (h a ((hmem hyO a).mpr haM))
  have h2 := congrArg (fun t => Y.presheaf.germ (Y.basicOpen f) y hyf (D.onSections t)) ham
  simp only [D.onSections_mul, D.onSections_restrict, map_add, map_mul, hgerm] at h2
  have h3 : Y.presheaf.germ O y hyO m * Y.presheaf.germ V y hyV (D.onSections s) ∈ M := by
    have he : Y.presheaf.germ O y hyO m * Y.presheaf.germ V y hyV (D.onSections s) =
        Y.presheaf.germ O y hyO (D.onSections a) -
          Y.presheaf.germ V y hyV s * Y.presheaf.germ O y hyO (D.onSections m) := by
      rw [← h2]
      ring
    rw [he]
    exact M.sub_mem hDaM (M.mul_mem_right _ hsM)
  exact (hmem hyV _).mpr ((Ideal.unit_mul_mem_iff_mem M hunit).mp h3) hDs

/-- A point of an affine open lies in a basic open exactly when the section is outside its prime. -/
private theorem fromSpec_mem_basicOpen_iff {O : Y.Opens} (hO : IsAffineOpen O)
    (q : PrimeSpectrum Γ(Y, O)) (b : Γ(Y, O)) : hO.fromSpec q ∈ Y.basicOpen b ↔ b ∉ q.asIdeal :=
  eq_iff_iff.mp (congrArg (fun W : (Spec Γ(Y, O)).Opens => q ∈ W)
    (hO.fromSpec_preimage_basicOpen b))

/-- **A vector field fixing every point of a fibre fixes every `k`-point of the stalk of the
direct image.** Let `ν : Y ⟶ X` be an affine morphism, with `Y` locally of finite type over `k`
through `ν` and the structure morphism of `X`, and let `D'` be a vector field on `Y` fixing every
closed point of `Y` above `x`. Then the derivation `D'` induces on `(ν_* 𝒪_Y)_x` fixes every
`k`-point `ε` of that stalk.

Given a germ killed by `ε`, represented over an affine open `U₀ ∋ x`, the kernel of `ε` on the
sections over the affine open `ν⁻¹ U₀` is a maximal ideal, hence a closed point `y` of `Y`
(a Jacobson space); `y` lies over `x` because `ε` restricts on `𝒪_{X, x}` to the residue map,
its kernel being a maximal ideal of a local ring. A section over `ν⁻¹ U₀` is killed by `ε`
exactly when it vanishes at `y`, so `D'` fixing `y` is what is needed. -/
theorem forall_fixes_stalkDerivation_of_forall_fixes (ν : Y ⟶ X) [IsAffineHom ν]
    {hX : X ⟶ Spec (.of k)} [LocallyOfFiniteType (ν ≫ hX)] (D' : SheafDerivationOf (ν ≫ hX))
    (x : X) (h : ∀ (y : Y) (hy : IsClosed ({y} : Set Y)), ν.base y = x → D'.Fixes y hy) :
    letI := directImageStalkFieldAlgebra ν hX x
    ∀ ε : ((ν.base _* Y.presheaf).stalk x) →ₐ[k] k,
      NodalVectorFields.Fixes ε (stalkDerivation ν D' x) := by
  let := directImageStalkFieldAlgebra ν hX x
  let := directImageStalkAlgebra ν x
  intro ε z hz
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (ν.base _* Y.presheaf) z
  obtain ⟨-, ⟨U₀, hU₀, rfl⟩, hxU₀, hU₀U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hle : U₀ ≤ U := hU₀U
  have hres : (ν.base _* Y.presheaf).germ U x hxU s =
      (ν.base _* Y.presheaf).germ U₀ x hxU₀
        (((ν.base _* Y.presheaf).map (homOfLE hle).op).hom s) :=
    ((ν.base _* Y.presheaf).germ_res_apply (homOfLE hle) x hxU₀ s).symm
  rw [hres] at hz ⊢
  rw [stalkDerivation_germ]
  set t : Γ(Y, ν ⁻¹ᵁ U₀) := ((ν.base _* Y.presheaf).map (homOfLE hle).op).hom s
  let φ : Γ(Y, ν ⁻¹ᵁ U₀) →+* k :=
    ε.toRingHom.comp ((ν.base _* Y.presheaf).germ U₀ x hxU₀).hom
  let ψ : X.presheaf.stalk x →+* k :=
    ε.toRingHom.comp (algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x))
  have hφψ : ∀ a : Γ(X, U₀), φ (ν.app U₀ a) = ψ (X.presheaf.germ U₀ x hxU₀ a) := fun a => by
    change ε _ = ε _
    congr 1
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U₀ x hxU₀ ν.c a).symm
  have htop : U₀ ≤ hX ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hψc : ∀ c : k, ψ (X.presheaf.germ (hX ⁻¹ᵁ ⊤) x trivial
      ((hX.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) = c := fun c => by
    have he : algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)
        (X.presheaf.germ (hX ⁻¹ᵁ ⊤) x trivial
          ((hX.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
        algebraMap k ((ν.base _* Y.presheaf).stalk x) c :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply (hX ⁻¹ᵁ ⊤) x trivial ν.c _
    change ε _ = c
    rw [he]
    exact ε.commutes c
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨ν.app U₀ ((X.presheaf.map (homOfLE htop).op).hom
      ((hX.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))), ?_⟩
    rw [hφψ]
    refine (congrArg ψ ?_).trans (hψc c)
    exact X.presheaf.germ_res_apply (homOfLE htop) x hxU₀ _
  have hker : ∀ t : X.presheaf.stalk x,
      ψ t = 0 ↔ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun t => by
    rw [← IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective ψ fun c => ⟨_, hψc c⟩), RingHom.mem_ker]
  have hO : IsAffineOpen (ν ⁻¹ᵁ U₀) := hU₀.preimage ν
  let q : PrimeSpectrum Γ(Y, ν ⁻¹ᵁ U₀) := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  have hqmax : q.asIdeal.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ
  let y : Y := hO.fromSpec q
  have hyO : y ∈ ν ⁻¹ᵁ U₀ := by
    have : y ∈ Set.range hO.fromSpec := ⟨q, rfl⟩
    rwa [hO.range_fromSpec] at this
  have hbasic : ∀ b : Γ(Y, ν ⁻¹ᵁ U₀), y ∈ Y.basicOpen b ↔ φ b ≠ 0 := fun b =>
    (fromSpec_mem_basicOpen_iff hO q b).trans (not_congr RingHom.mem_ker)
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (ν ≫ hX)
  have hy : IsClosed ({y} : Set Y) := by
    have hq : q ∈ closedPoints (Spec Γ(Y, ν ⁻¹ᵁ U₀)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hqmax
    rw [← hO.fromSpec.isOpenEmbedding.preimage_closedPoints] at hq
    exact hq
  have hxy : ν.base y = x := by
    have hνy : ν.base y ∈ U₀ := hyO
    have key : ∀ a : Γ(X, U₀), ν.base y ∈ X.basicOpen a ↔ x ∈ X.basicOpen a := fun a => by
      have h1 : ν.base y ∈ X.basicOpen a ↔ y ∈ ν ⁻¹ᵁ X.basicOpen a := Iff.rfl
      rw [h1, Scheme.preimage_basicOpen, hbasic, hφψ, Scheme.mem_basicOpen X a x hxU₀, Ne,
        hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hmemP : ∀ (w : X) (hw : w ∈ U₀) (a : Γ(X, U₀)),
        a ∈ (hU₀.primeIdealOf ⟨w, hw⟩).asIdeal ↔ w ∉ X.basicOpen a := fun w hw a => by
      have he := fromSpec_mem_basicOpen_iff hU₀ (hU₀.primeIdealOf ⟨w, hw⟩) a
      rw [hU₀.fromSpec_primeIdealOf] at he
      rw [he, not_not]
    have hp : hU₀.primeIdealOf ⟨ν.base y, hνy⟩ = hU₀.primeIdealOf ⟨x, hxU₀⟩ := by
      ext a
      rw [hmemP, hmemP, key]
    have he := congrArg hU₀.fromSpec hp
    rwa [hU₀.fromSpec_primeIdealOf, hU₀.fromSpec_primeIdealOf] at he
  have hfix := (D'.fixes_iff_basicOpen y hy).mp (h y hy hxy)
  have hz' : y ∉ Y.basicOpen t := by
    rw [hbasic, not_not]
    exact hz
  have hD := hfix ⟨ν ⁻¹ᵁ U₀, hO⟩ t hz'
  rw [hbasic, not_not] at hD
  exact hD

/-- **A vector field whose induced derivation fixes the `k`-points of the stalk of the direct
image fixes the points of the fibre.** Let `k` be algebraically closed, let `ν : Y ⟶ X` be an
affine morphism with `Y` locally of finite type over `k` through `ν` and the structure morphism
of `X`, and let `y` be a closed point of `Y`. If the derivation that a vector field `D'` induces
on `(ν_* 𝒪_Y)_{ν(y)}` fixes every `k`-point of that stalk, then `D'` fixes `y`.

This is the converse of `Stacks.Curves.fixes_stalkDerivation_of_fixes`. The residue at `y` is a
`k`-point of the stalk (`Stacks.Curves.exists_algHom_apply_germ_eq_zero_iff_notMem_basicOpen`),
which gives the condition on the sections over the preimage of one affine open around `ν(y)`,
and `Stacks.Curves.SheafDerivationOf.fixes_of_isAffineOpen` spreads it to every affine open. -/
theorem fixes_of_forall_fixes_stalkDerivation [IsAlgClosed k] (ν : Y ⟶ X) [IsAffineHom ν]
    {hX : X ⟶ Spec (.of k)} [LocallyOfFiniteType (ν ≫ hX)] (D' : SheafDerivationOf (ν ≫ hX))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (h : letI := directImageStalkFieldAlgebra ν hX (ν.base y)
      ∀ ε : ((ν.base _* Y.presheaf).stalk (ν.base y)) →ₐ[k] k,
        NodalVectorFields.Fixes ε (stalkDerivation ν D' (ν.base y))) :
    D'.Fixes y hy := by
  let : Y.Over (Spec (.of k)) := ⟨ν ≫ hX⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType (ν ≫ hX)›
  let := directImageStalkFieldAlgebra ν hX (ν.base y)
  obtain ⟨ε, hε⟩ :=
    exists_algHom_apply_germ_eq_zero_iff_notMem_basicOpen k hX ν rfl y hy (ν.base y) rfl
  obtain ⟨-, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show ν.base y ∈ ((⊤ : X.Opens) : Set X) from trivial) (⊤ : X.Opens).2
  refine D'.fixes_of_isAffineOpen y hy (hU₀.preimage ν) hxU₀ fun s hs => ?_
  have h1 := h ε _ ((hε U₀ hxU₀ s).mpr hs)
  rw [stalkDerivation_germ] at h1
  exact (hε U₀ hxU₀ _).mp h1

end Fixing

section Tag

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **The extension of a vector field to the normalization fixes the points over every node.**
Let `k` be algebraically closed and `X` a reduced one-dimensional `k`-scheme, locally of finite
type, with affine diagonal and at worst nodal singularities. Then a vector field `D` on `X` has
a unique extension `D'` to the normalization, and at every node `x` of `X` the derivation that
`D'` induces on `(ν_* 𝒪_{X^ν})_x` fixes every `k`-point of that stalk.

The extension and its uniqueness are
`Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities`. That it fixes
the `k`-points is `Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode`, applied
to the derivation `D'` induces on the stalk, which restricts to the one `D` induces on
`𝒪_{X, x}` by `Stacks.Curves.stalkDerivation_algebraMap_eq_of_extension`. -/
theorem existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (D : SheafDerivationOf (X ↘ Spec (.of k))) :
    ∃! D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))),
      (∀ (U : X.Opens) (s : Γ(X, U)),
          D'.onSections (((Scheme.normalization X hfin).app U).hom s)
            = ((Scheme.normalization X hfin).app U).hom (D.onSections s)) ∧
        ∀ x : X, IsNode k X x →
          letI : Algebra k (X.presheaf.stalk x) :=
            (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
          letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin)
            (X ↘ Spec (.of k)) x
          ∀ ε : (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
            NodalVectorFields.Fixes ε
              (stalkDerivation (Scheme.normalization X hfin) D' x) := by
  obtain ⟨D', hD', huniq⟩ :=
    existsUnique_extend_normalization_of_hasAtWorstNodalSingularities k X hfin hdim hnodal D
  refine ⟨D', ⟨hD', fun x hnode => ?_⟩, fun D₂ h₂ => huniq D₂ h₂.1⟩
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
  exact forall_fixes_of_extend_normalizationStalk_of_isNode k X hfin hdim x hnode
    (ownStalkDerivation D x) (stalkDerivation (Scheme.normalization X hfin) D' x)
    (stalkDerivation_algebraMap_eq_of_extension (Scheme.normalization X hfin)
      (X ↘ Spec (.of k)) D D' hD' x)

/-- **Vector fields on a nodal curve and on its normalization, without properness.** Let `k` be
an algebraically closed field and let `X` be a reduced one-dimensional `k`-scheme, locally of
finite type, with affine diagonal and at worst nodal singularities, whose quasi-compact opens
have finitely many irreducible components, and let `ν : X^ν ⟶ X` be its normalization. Then
```
Der_k(𝒪_X, 𝒪_X) = {D' ∈ Der_k(𝒪_{X^ν}, 𝒪_{X^ν}) | D' fixes every point of X^ν over a node},
```
the equality being read through the injection `ν^♯` of `𝒪_X` into `ν_* 𝒪_{X^ν}`: the two
clauses say that every vector field on `X` has a unique extension to `X^ν`, that the extension
fixes the points over the nodes, and that conversely every vector field on `X^ν` fixing those
points is the extension of a unique vector field on `X`.

"Fixing the points of `X^ν` over the node `x`" is rendered as fixing every `k`-point of the
stalk `(ν_* 𝒪_{X^ν})_x`; at a node those are the residues at the two points above `x`. It is
the same condition in both clauses.

This is Tag 0E68 in greater generality: a proper `X` satisfies every assumption here, which is
how `Stacks.Curves.NodalVectorFields.range_branchPair` deduces the tag from it. The
regular-or-nodal dichotomy at the points of `X`, the splitness of the nodes and the two branch
residues are all derived from `Stacks.Curves.HasAtWorstNodalSingularities`. -/
theorem derivations_eq_normalization_derivations_fixing_nodes
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    (∀ D : SheafDerivationOf (X ↘ Spec (.of k)),
        ∃! D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))),
          (∀ (U : X.Opens) (s : Γ(X, U)),
              D'.onSections (((Scheme.normalization X hfin).app U).hom s)
                = ((Scheme.normalization X hfin).app U).hom (D.onSections s)) ∧
            ∀ x : X, IsNode k X x →
              letI : Algebra k (X.presheaf.stalk x) :=
                (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
              letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin)
                (X ↘ Spec (.of k)) x
              ∀ ε : (((Scheme.normalization X hfin).base _*
                  (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
                NodalVectorFields.Fixes ε
                  (stalkDerivation (Scheme.normalization X hfin) D' x)) ∧
      ∀ D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))),
        (∀ x : X, IsNode k X x →
            letI : Algebra k (X.presheaf.stalk x) :=
              (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
            letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin)
              (X ↘ Spec (.of k)) x
            ∀ ε : (((Scheme.normalization X hfin).base _*
                (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
              NodalVectorFields.Fixes ε
                (stalkDerivation (Scheme.normalization X hfin) D' x)) →
          ∃! D : SheafDerivationOf (X ↘ Spec (.of k)), ∀ (U : X.Opens) (s : Γ(X, U)),
            D'.onSections (((Scheme.normalization X hfin).app U).hom s)
              = ((Scheme.normalization X hfin).app U).hom (D.onSections s) := by
  refine ⟨existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities k X hfin hdim
    hnodal, fun D' h => ?_⟩
  obtain ⟨D, hD, huniq⟩ :=
    existsUnique_descend_normalization_of_hasAtWorstNodalSingularities k X hfin hdim hnodal D' h
  exact ⟨D, fun U s => (hD U s).symm, fun D₂ h₂ => huniq D₂ fun U s => (h₂ U s).symm⟩

end Tag

section NonIsoLocus

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)

/-- **Away from the nodes, a nodal curve is smooth.** On a reduced scheme of dimension one,
locally of finite type over an algebraically closed field and with at worst nodal singularities,
every point that is not a node is a smooth point: a closed point by the definition of
at-worst-nodal singularities, and a point that is not closed because its local ring is a field,
hence regular, and over a perfect field regularity is smoothness (Tag 0B8X). -/
theorem smoothAt_of_not_isNode [IsReduced X] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (x : X) (hx : ¬ IsNode k X x) :
    InfinitesimalLifting.SmoothAt (X ↘ Spec (.of k)) x := by
  by_cases hcl : IsClosed ({x} : Set X)
  · exact (hnodal x hcl).resolve_right hx
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hbound : ∀ z : X, Order.coheight z ≤ 1 := by
    intro z
    have h : ((Order.coheight z : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      exact (AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim z).trans (le_of_eq hdim)
    exact WithBot.coe_le_coe.mp h
  have hmax : IsMax x := by
    rw [← Order.coheight_eq_zero]
    obtain ⟨z, hz, hzne⟩ : ∃ z ∈ closure ({x} : Set X), z ≠ x := by
      by_contra hc
      push Not at hc
      exact hcl (closure_eq_iff_isClosed.mp
        (Set.Subset.antisymm (fun z hz => hc z hz) subset_closure))
    have hzle : z ≤ x := specializes_iff_mem_closure.mpr hz
    have hzlt : z < x :=
      ⟨hzle, fun hxz => hzne ((hxz : Specializes z x).antisymm (hzle : Specializes x z)).eq⟩
    have hlt : Order.coheight x < Order.coheight z :=
      Order.coheight_strictAnti hzlt (lt_of_le_of_lt (hbound x) (by simp))
    simpa using hlt.trans_le (hbound z)
  have hfield : IsField (X.presheaf.stalk x) := AlgebraicGeometry.isField_stalk_of_isMax hmax
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
    simpa using ringKrullDim_nonneg_of_nontrivial (R := X.presheaf.stalk x)
  have he := congrArg (x ∈ ·) (smoothAt_locus_eq_regular_locus k (X ↘ Spec (.of k)))
  exact (eq_iff_iff.mp he).mpr hreg

/-- **The normalization of a nodal curve is an isomorphism away from the nodes.** On a reduced
one-dimensional scheme, locally of finite type over an algebraically closed field and with at
worst nodal singularities, a point `x` that is not a node has an open neighbourhood over which
the normalization `ν` restricts to an isomorphism: a smooth open neighbourhood, which is normal
(Tag 033C), and `ν` is an isomorphism over every normal open. -/
theorem exists_isIso_normalization_restrict_of_not_isNode [IsReduced X]
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X) (x : X)
    (hx : ¬ IsNode k X x) :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (Scheme.normalization X hfin ∣_ U) := by
  obtain ⟨U, hxU, hsm⟩ := smoothAt_of_not_isNode k X hdim hnodal x hx
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal (⊤ : (Spec (.of k)).Opens).toScheme := isNormal_of_iso (Spec (.of k)).topIso
  have : IsNormal U.toScheme := isNormal_of_smooth ((X ↘ Spec (.of k)).resLE ⊤ U le_top)
  exact ⟨U, hxU, Scheme.isIso_normalization_restrict_of_isNormal X hfin U this⟩

/-- **The normalization of a nodal curve is an isomorphism over no neighbourhood of a node.**
If `ν` restricted over an open `U` containing a node `x` were an isomorphism, the local ring
`𝒪_{X, x}` would be isomorphic to a local ring of the normal scheme `X^ν`, hence a normal domain;
but the image of a nodal local ring in its normalization is a proper submodule
(`Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra`). -/
theorem not_isIso_normalization_restrict_of_isNode (y : Scheme.normalizationScheme X hfin)
    (hy : IsNode k X ((Scheme.normalization X hfin).base y)) (U : X.Opens)
    (hyU : (Scheme.normalization X hfin).base y ∈ U) :
    ¬ IsIso (Scheme.normalization X hfin ∣_ U) := by
  intro hiso
  set ν := Scheme.normalization X hfin
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have h1 : IsIso ((ν ∣_ U).stalkMap ⟨y, hyU⟩) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (ν ∣_ U))).2 _
  have h2 : IsIso (ν.stalkMap y) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap ν U ⟨y, hyU⟩)).mp h1
  have : IsNormal (Scheme.normalizationScheme X hfin) := Scheme.isNormal_normalizationScheme X hfin
  let e : X.presheaf.stalk (ν.base y) ≃+* (Scheme.normalizationScheme X hfin).presheaf.stalk y :=
    (asIso (ν.stalkMap y)).commRingCatIsoToRingEquiv
  have : IsDomain (X.presheaf.stalk (ν.base y)) :=
    Function.Injective.isDomain e.toRingHom e.injective
  have : IsIntegrallyClosed ((Scheme.normalizationScheme X hfin).presheaf.stalk y) :=
    IsNormal.stalk_normal y
  have : IsIntegrallyClosed (X.presheaf.stalk (ν.base y)) := IsIntegrallyClosed.of_equiv e.symm
  let : Algebra k (X.presheaf.stalk (ν.base y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ (ν.base y) (by simp)).hom.toAlgebra
  have hA := (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X (ν.base y) hy.isClosed).mp hy
  have hc := isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k _ hA
  refine hc.1 (eq_top_iff.mpr fun b _ => ?_)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp b.2
  exact ⟨a, Subtype.ext ha⟩

omit [IsAlgClosed k] in
/-- **The points of the normalization above a node are closed.** The fibre of the finite
morphism `ν` over the closed point `x` is finite, so the closed points of the closure of a point
`y` of it form a finite, hence closed, set; `X^ν` being a Jacobson space, that set is the whole
closure, which therefore consists of closed points and contains `y`. -/
theorem isClosed_singleton_of_isNode (y : Scheme.normalizationScheme X hfin)
    (hy : IsNode k X ((Scheme.normalization X hfin).base y)) : IsClosed ({y} : Set _) := by
  set ν := Scheme.normalization X hfin
  have : IsFinite ν := isFinite_normalizationOverField k (X ↘ Spec (.of k))
  have : JacobsonSpace (Scheme.normalizationScheme X hfin) :=
    LocallyOfFiniteType.jacobsonSpace (ν ≫ (X ↘ Spec (.of k)))
  set F := ν.base ⁻¹' {ν.base y}
  have hF : F.Finite := ν.finite_preimage_singleton (ν.base y)
  have hFcl : IsClosed F := hy.isClosed.preimage ν.base.hom.continuous
  set Z := closure ({y} : Set (Scheme.normalizationScheme X hfin))
  have hZF : Z ⊆ F := closure_minimal (Set.singleton_subset_iff.mpr rfl) hFcl
  have hcl : IsClosed (Z ∩ closedPoints _) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints _)]
    exact (hF.subset (Set.inter_subset_left.trans hZF)).isClosed_biUnion fun z hz => hz.2
  have hZ : Z ∩ closedPoints _ = Z := by
    have h := closure_inter_closedPoints (isClosed_closure : IsClosed Z)
    rwa [hcl.closure_eq] at h
  have hyZ : y ∈ Z ∩ closedPoints _ := by
    rw [hZ]
    exact subset_closure (Set.mem_singleton y)
  exact hyZ.2

/-- **The points where the normalization of a nodal curve is not an isomorphism are the points
above the nodes.** For `y` a point of `X^ν`, there is no open neighbourhood of `ν(y)` over which
`ν` restricts to an isomorphism exactly when `ν(y)` is a node of `X`. -/
theorem not_exists_isIso_normalization_restrict_iff [IsReduced X]
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (y : Scheme.normalizationScheme X hfin) :
    (¬ ∃ U : X.Opens, (Scheme.normalization X hfin).base y ∈ U ∧
        IsIso (Scheme.normalization X hfin ∣_ U)) ↔
      IsNode k X ((Scheme.normalization X hfin).base y) := by
  refine ⟨fun h => ?_, fun hy ⟨U, hyU, hiso⟩ =>
    not_isIso_normalization_restrict_of_isNode k X hfin y hy U hyU hiso⟩
  by_contra hn
  exact h (exists_isIso_normalization_restrict_of_not_isNode k X hfin hdim hnodal _ hn)

end NonIsoLocus

section Proper

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- **Stacks Project, Tag 0E68.** Let `k` be an algebraically closed field, let `X` be a proper
one-dimensional `k`-scheme with at worst nodal singularities, let `ν : X^ν ⟶ X` be its
normalization and let `S ⊆ X^ν` be the set of points where `ν` is not an isomorphism: the points
`y` such that `ν` restricts to an isomorphism over no open neighbourhood of `ν(y)`. Then
```
Der_k(𝒪_X, 𝒪_X) = {D' ∈ Der_k(𝒪_{X^ν}, 𝒪_{X^ν}) | D' fixes every x^ν ∈ S},
```
the equality being read through the injection `ν^♯` of `𝒪_X` into `ν_* 𝒪_{X^ν}`. The first
clause says that every vector field `D` on `X` has a unique extension `D'` to `X^ν`, that is a
vector field with `D' (ν^♯ s) = ν^♯ (D s)` for every local section `s`, and that `D'` fixes every
point of `S`; the second says that every vector field on `X^ν` fixing every point of `S` is the
extension of a unique vector field on `X`. "Fixes" is the notion of Section 53.26,
`Stacks.Curves.SheafDerivationOf.Fixes`: the point is closed and its ideal sheaf is carried into
itself.

`S` is exactly the set of points above the nodes of `X`
(`Stacks.Curves.not_exists_isIso_normalization_restrict_iff`): away from the nodes `X` is smooth,
hence normal, and `ν` is an isomorphism over every normal open; over no neighbourhood of a node
is it one, because the local ring at a node is not a normal domain. The points of `S` are closed
(`Stacks.Curves.isClosed_singleton_of_isNode`).

The normalization is formed with the finiteness of irreducible components of quasi-compact opens
that every scheme locally of finite type over a field enjoys
(`AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType`). The source also
assumes `X` connected; the statement holds without it. The proof derives from properness and
nodality what `Stacks.Curves.derivations_eq_normalization_derivations_fixing_nodes` needs: `X`
is reduced (`Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities`) and, being separated over
the affine scheme `Spec k`, has affine diagonal. That lemma states the fixing condition on the
stalks of `ν_* 𝒪_{X^ν}` at the nodes, and the two are exchanged by
`Stacks.Curves.fixes_of_forall_fixes_stalkDerivation` and
`Stacks.Curves.forall_fixes_stalkDerivation_of_forall_fixes`, `ν` being finite
(`AlgebraicGeometry.isFinite_normalizationOverField`). -/
@[stacks 0E68]
theorem NodalVectorFields.range_branchPair (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    (∀ D : SheafDerivationOf (X ↘ Spec (.of k)),
        ∃! D' : SheafDerivationOf (Scheme.normalization X
            (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))) ≫
              (X ↘ Spec (.of k))),
          (∀ (U : X.Opens) (s : Γ(X, U)),
              D'.onSections ((Scheme.normalization X
                  (finite_irreducibleComponents_of_locallyOfFiniteType k
                    (X ↘ Spec (.of k)))).app U |>.hom s) =
                ((Scheme.normalization X
                  (finite_irreducibleComponents_of_locallyOfFiniteType k
                    (X ↘ Spec (.of k)))).app U).hom (D.onSections s)) ∧
            ∀ y : Scheme.normalizationScheme X
                (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))),
              (¬ ∃ U : X.Opens,
                (Scheme.normalization X
                  (finite_irreducibleComponents_of_locallyOfFiniteType k
                    (X ↘ Spec (.of k)))).base y ∈ U ∧
                IsIso (Scheme.normalization X
                  (finite_irreducibleComponents_of_locallyOfFiniteType k
                    (X ↘ Spec (.of k))) ∣_ U)) →
              ∃ hy : IsClosed ({y} : Set _), D'.Fixes y hy) ∧
      ∀ D' : SheafDerivationOf (Scheme.normalization X
          (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))) ≫
            (X ↘ Spec (.of k))),
        (∀ y : Scheme.normalizationScheme X
            (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))),
          (¬ ∃ U : X.Opens,
            (Scheme.normalization X
              (finite_irreducibleComponents_of_locallyOfFiniteType k
                (X ↘ Spec (.of k)))).base y ∈ U ∧
            IsIso (Scheme.normalization X
              (finite_irreducibleComponents_of_locallyOfFiniteType k
                (X ↘ Spec (.of k))) ∣_ U)) →
          ∃ hy : IsClosed ({y} : Set _), D'.Fixes y hy) →
          ∃! D : SheafDerivationOf (X ↘ Spec (.of k)), ∀ (U : X.Opens) (s : Γ(X, U)),
            D'.onSections ((Scheme.normalization X
                (finite_irreducibleComponents_of_locallyOfFiniteType k
                  (X ↘ Spec (.of k)))).app U |>.hom s) =
              ((Scheme.normalization X
                (finite_irreducibleComponents_of_locallyOfFiniteType k
                  (X ↘ Spec (.of k)))).app U).hom (D.onSections s) := by
  set hfin := finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsSeparated (terminal.from X) := by
    have : IsSeparated ((X ↘ Spec (.of k)) ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : IsFinite (Scheme.normalization X hfin) :=
    isFinite_normalizationOverField k (X ↘ Spec (.of k))
  have hS := not_exists_isIso_normalization_restrict_iff k X hfin hdim hnodal
  obtain ⟨h1, h2⟩ := derivations_eq_normalization_derivations_fixing_nodes k X hfin hdim hnodal
  refine ⟨fun D => ?_, fun D' hD' => h2 D' fun x hx =>
    forall_fixes_stalkDerivation_of_forall_fixes _ D' x fun y _ hxy =>
      (hD' y ((hS y).mpr (hxy ▸ hx))).snd⟩
  obtain ⟨D', ⟨hc, hfix⟩, huniq⟩ := h1 D
  refine ⟨D', ⟨hc, fun y hyS =>
      ⟨isClosed_singleton_of_isNode k X hfin y ((hS y).mp hyS),
        fixes_of_forall_fixes_stalkDerivation _ D' y _ (hfix _ ((hS y).mp hyS))⟩⟩,
    fun D₂ h₂ => huniq D₂ ⟨h₂.1, fun x hx => ?_⟩⟩
  exact forall_fixes_stalkDerivation_of_forall_fixes _ D₂ x fun y _ hxy =>
    (h₂.2 y ((hS y).mpr (hxy ▸ hx))).snd

end Proper

end Stacks.Curves

end
