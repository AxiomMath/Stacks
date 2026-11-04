module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTensorCompatibility
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseModuleSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistSheafMultiplication

/-!
# Tag 0B5J: the Veronese comparison of projective spectra, in one statement

Let `S` be a graded ring and `d ≥ 1`. Write `S' = S⁽ᵈ⁾` for the Veronese subring
`⨁ₙ S_{nd}`, `X = Proj S` and `X' = Proj S'`. The tag asserts that the ring inclusion
`S' ⊆ S` induces an isomorphism of schemes `i : X ⟶ X'`, under which the associated sheaf of
every graded `S`-module `M` becomes the pullback of the associated sheaf of `M' = M⁽ᵈ⁾`, the
twist `𝒪_X(nd)` becomes the pullback of `𝒪_{X'}(n)`, and these identifications are compatible
with the multiplication maps of Tag 01MK and hence with the maps of Tags 01MO, 03GJ, 01MP, 03GK,
01MQ and 01MR.

`Stacks.Veronese.tag0B5J` states all of that as a single theorem under the tag's own two
hypotheses. Its conjuncts are:

1. `i` is an isomorphism of schemes, and it is *the* map induced by `S' ⊆ S`: on a homogeneous
   prime `x` of `S` it is contraction, `i(x) = S' ∩ x`, and on each standard open
   `D₊(f) = Spec S₍f₎` it is `Spec` of the canonical identification `S'₍f ᵈ₎ ≅ S₍f₎` followed by
   the inclusion of `D₊(f ᵈ)`. The charts cover `Proj S`, so they determine `i`.
2. The chart identification: `i⁻¹ D₊(f ᵈ) = D₊(f)` for every positive-degree homogeneous `f`.
   This is the source's "`f ∈ S₊` homogeneous and `f ∉ 𝔭` give `f ᵈ ∈ S'₊` and `f ᵈ ∉ 𝔭'`", and
   it is what makes the chart descriptions of the next two conjuncts statable.
3. Assertion (1): for every graded `S`-module `M`, whose carrier may lie in any universe, the
   isomorphism `Stacks.Veronese.veroneseAssociatedSheafIso : M̃ ≅ i^*(M'~)` is canonical — on
   each `D₊(f)` its inverse carries the pullback of the section `m / (f ᵈ)ⁿ` of `M'~` to the
   section `m / f^(nd)` of `M̃`, i.e. it is the degree-zero Veronese localization comparison
   `M'₍f ᵈ₎ ≅ M₍f₎` of the source's "we have `M₍f₎ ≅ M'₍f ᵈ₎`".
4. Assertion (2): the isomorphisms `𝒪_X(nd) ≅ i^*𝒪_{X'}(n)`, each exhibited as the source
   exhibits it — conjunct 3 at `M = S(nd)`, followed by the canonical identification
   `(S(nd))⁽ᵈ⁾ ≅ S'(n)` of graded `S'`-modules.
5. Compatibility with the multiplication maps of Tag 01MK: the square of
   `ProjVeroneseTensorCompatibility.lean` commutes for every pair of graded `S`-modules.
6. The compatibilities the tag derives from it ("and hence with the maps (01MO), (03GJ), (01MP),
   (03GK), (01MQ), and (01MR)"), whose precise form the source leaves to its proof and then
   omits. Each is the square in which the isomorphisms of (1) and (2) carry the map on `X'` to
   the map on `X`:
   * (01MO) `𝒪_X(nd) ⊗ 𝒪_X(md) ⟶ 𝒪_X((n+m)d)` against `𝒪_{X'}(n) ⊗ 𝒪_{X'}(m) ⟶ 𝒪_{X'}(n+m)`,
     through (2) and Tag 01CD (`veroneseTwistMulCompatibility`);
   * (03GJ) `𝒪_X(nd) ⊗ ℱ(md) ⟶ ℱ((n+m)d)` against `𝒪_{X'}(n) ⊗ ℱ'(m) ⟶ ℱ'(n+m)` for every
     `𝒪_{X'}`-module `ℱ'` and `ℱ = i^*ℱ'`, through (2), its transport
     `veroneseTwistedModuleIso : ℱ(md) ≅ i^*(ℱ'(m))` and Tag 01CD
     (`veroneseTwistSheafMulCompatibility`);
   * (01MP) the graded ring map `S → ⨁ₙ Γ(X, 𝒪_X(n))` in degree `nd` against
     `S' → ⨁ₙ Γ(X', 𝒪_{X'}(n))` in degree `n`, through (2) on global sections
     (`veroneseGlobalSectionsRingMapCompatibility`);
   * (03GK) the products of global sections of `𝒪(nd)` and `ℱ(md)`, which define the module
     structure of Tag 03GK, against those of `𝒪'(n)` and `ℱ'(m)`
     (`veroneseMultiplyHomogeneousSectionsCompatibility`, for all integers `n`; for `n ≥ 0`
     these are the products of Tag 03GK by `multiplyHomogeneousSections_eq_prime`);
   * (01MQ) `M̃ ⊗ 𝒪_X(nd) ⟶ M(nd)~` against `M'~ ⊗ 𝒪_{X'}(n) ⟶ M'(n)~`, through (1) for `M`
     and for `M(nd)` (followed by `M(nd)' = M'(n)`), (2) and Tag 01CD
     (`veroneseModuleTwistCompatibility`);
   * (01MR) the graded module map `M → ⨁ₙ Γ(X, M(n)~)` in degree `nd` against
     `M' → ⨁ₙ Γ(X', M'(n)~)` in degree `n`, through `M(nd)~ ≅ i^*(M'(n)~)`, for a module in any
     universe (`veroneseGlobalSectionsModuleMapCompatibilityAny`).

## An erratum in the source's proof

The source argues conjunct 5 from the assertion that
`M' ⊗_{S'} N' = (M ⊗_S N)⁽ᵈ⁾` "as can be verified directly from the definitions". That is
false: `Stacks.Veronese.not_injective_veroneseTensorMap` proves that the comparison
`c = Stacks.Veronese.veroneseTensorMap` — the very map along the lower edge of conjunct 5 — is
not injective at `S = k[x, y]`, `d = 2`, `M = N = S(1)`, killing the nonzero element
`x ⊗ y - y ⊗ x` of degree zero (in that degree `c` is the multiplication `S₁ ⊗_k S₁ ⟶ S₂`,
`Stacks.Veronese.not_injective_multiplicationDegreeOne`); so the square the source draws does
not even typecheck as drawn. The square does commute with the canonical comparison
`c : M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` inserted along its lower edge: over every standard open
`D₊(f) = i⁻¹ D₊(f ᵈ)` both of its composites send `m / f^(pd) ⊗ n / f^(qd)` to
`c(m ⊗ n) / (f ᵈ)^(p+q)`. That is how conjunct 5 is stated here, and
`Stacks.Veronese.veroneseLocalizedModuleFun_veroneseTensorMap_mk` is the identity of fractions
that makes it work. The defect is in the source's argument, not in its statement.

## Universes

The graded ring lives in `Type u` and a graded module in `Type v`, independently. For a module
in `Type v` the associated sheaves on `Proj S` and on `Proj S'` have their sections in
`Type (max u v)`, and the pullback `i^*` of conjunct 3 is `SheafOfModules.pullback.{max u v}`,
the left adjoint of the pushforward of such sheaves along `i`
(`AlgebraicGeometry.Scheme.Hom.pushforward_isRightAdjoint_anyUniverse`); at `v = u` it is
`AlgebraicGeometry.Scheme.Modules.pullback` by definition. The compatibility with Tag 01MR is
likewise stated for modules in any universe, as the map of Tag 01MR is. The twists of
conjunct 4 are the sheaves of the graded modules `S(nd)` and `S'(n)`, which lie in the universe
of the ring. The maps of Tags 01MK, 01MQ and 03GJ are, as the library defines them, morphisms
out of tensor products of sheaves of modules with sections in the universe of the ring — their
own carriers take `M N : Type u` and `ℱ : SheafOfModules.{u}` — so the compatibilities with them
are stated for such modules; on a module in `Type u` the isomorphism of conjunct 3 is
`Stacks.Veronese.associatedModuleSheafVeroneseIso`, which is `veroneseAssociatedSheafIso` by
definition.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 00JL](https://stacks.math.columbia.edu/tag/00JL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (tensorGrading shiftedGrading)

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **[Stacks, Tag 0B5J].** Let `S` be a graded ring and `d ≥ 1`. Set `S' = S⁽ᵈ⁾`,
`X = Proj S` and `X' = Proj S'`. There is a canonical isomorphism `i : X ⟶ X'` of schemes such
that (1) for any graded `S`-module `M`, setting `M' = M⁽ᵈ⁾`, there is a canonical isomorphism
`M̃ ≅ i^*(M'~)`, and (2) there are canonical isomorphisms `𝒪_X(nd) ≅ i^*𝒪_{X'}(n)`; and these
isomorphisms are compatible with the multiplication maps of Tag 01MK and hence with the maps of
Tags 01MO, 03GJ, 01MP, 03GK, 01MQ and 01MR.

The isomorphism `i` is `Stacks.Veronese.veroneseProjIso 𝒮 d hd`, glued from the chart
isomorphisms; the first conjunct says its underlying morphism `veroneseProjHom` is an
isomorphism of schemes, that on homogeneous primes it is contraction along `S' ⊆ S`, and that on
each standard open `D₊(f) = Spec S₍f₎` it is `Spec` of the identification `S'₍f ᵈ₎ ≅ S₍f₎`
followed by the inclusion of `D₊(f ᵈ)` — the source's "`S₍f₎ ≅ S'₍f ᵈ₎`, compatible with the
restriction maps". These charts cover `Proj S`, so they determine `i` as a morphism of schemes,
not only on points. The next conjunct is the consequence `i⁻¹ D₊(f ᵈ) = D₊(f)`, which the
chart descriptions of assertion (1) are written over. The third conjunct is assertion (1) for a
module in any universe `v`: the
isomorphism `Stacks.Veronese.veroneseAssociatedSheafIso 𝒮 𝒨 d hd : M̃ ≅ i^*(M'~)`, with the
chart description that makes it canonical — on `D₊(f)` its inverse is the degree-zero Veronese
localization comparison `M'₍f ᵈ₎ ≅ M₍f₎`. The fourth conjunct is assertion (2), each isomorphism
exhibited as the source derives it: (1) at `M = S(nd)` followed by `(S(nd))⁽ᵈ⁾ ≅ S'(n)`. The
remaining conjuncts are the trailing clause: the commuting square with the multiplication maps
of Tag 01MK, and the six squares with the maps of Tags 01MO, 03GJ, 01MP, 03GK, 01MQ and 01MR
which the source derives from it and whose precise statements it omits. See the module
documentation for each square, for why the source's proof of the first is corrected here
(the comparison along its lower edge is not injective at `S = k[x, y]`, `d = 2`,
`M = N = S(1)`: `Stacks.Veronese.not_injective_veroneseTensorMap`), and for the universes. -/
@[stacks 0B5J "the canonical isomorphism i : Proj S to Proj S^(d) induced by the inclusion \
S^(d) in S, described on homogeneous primes and on the standard opens D+(f) = Spec S_(f); \
assertion (1), the canonical isomorphism from the sheaf of a graded S-module M, in any \
universe, to the pullback \
of the sheaf of M^(d), described on the standard opens; assertion (2), the isomorphisms \
O_X(nd) to i^* O_X'(n) obtained from (1) at M = S(nd); and the compatibility of these \
isomorphisms with the multiplication maps of associated sheaves (through the comparison map \
from M^(d) tensor N^(d) to (M tensor N)^(d)), with the multiplication of twists, with the maps \
O(n) tensor F(m) to F(n+m) and M~ tensor O(n) to M(n)~, with the maps from S and from M to \
twisted global sections, and with the products of twisted global sections",
  ega "II 8.14.13" "partial"]
theorem tag0B5J (d : ℕ) (hd : 1 ≤ d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    -- `i` is an isomorphism of schemes, and on homogeneous primes it is contraction along
    -- `S⁽ᵈ⁾ ⊆ S`
    IsIso (veroneseProjHom 𝒮 d hd) ∧
      (∀ (x : ProjectiveSpectrum 𝒮) (g : veroneseSubring 𝒮 d),
        g ∈ ((veroneseProjIso 𝒮 d hd).hom.base x).asHomogeneousIdeal ↔
          (g : S) ∈ x.asHomogeneousIdeal) ∧
      -- on each chart `D₊(f) = Spec S₍f₎`, `i` is `Spec` of `S'₍f ᵈ₎ ≅ S₍f₎` followed by the
      -- inclusion of `D₊(f ᵈ)`: these determine `i` as a morphism of schemes
      (∀ (f : S) (e : ℕ) (he : 0 < e) (hf : f ∈ 𝒮 e),
        Proj.awayι 𝒮 f hf he ≫ (veroneseProjIso 𝒮 d hd).hom =
          Spec.map (veroneseAwayEquiv 𝒮 d f hf hd).toCommRingCatIso.hom ≫
            Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
              (veronesePower_mem 𝒮 d f hf) he) ∧
      -- the chart identification `i⁻¹ D₊(f ᵈ) = D₊(f)`
      (∀ (f : S) (e : ℕ), 0 < e → ∀ hf : f ∈ 𝒮 e,
        (veroneseProjIso 𝒮 d hd).hom ⁻¹ᵁ
            Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf) =
          Proj.basicOpen 𝒮 f) ∧
      -- assertion (1): `veroneseAssociatedSheafIso 𝒮 𝒨 d hd : M̃ ≅ i^*(M'~)`, for a module in
      -- any universe, with the chart description that makes it the canonical isomorphism
      (∀ (M : Type v) [AddCommGroup M] [Module S M] (𝒨 : ℤ → AddSubgroup M)
          [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨],
        letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
        ∀ (f : S) (e : ℕ) (he : 0 < e) (hf : f ∈ 𝒮 e)
          (hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e)
          (z : GradedModuleDegreeZeroLocalization (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d) (veronesePower 𝒮 d f hf)),
          ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he
              ((veroneseAssociatedSheafIso 𝒮 𝒨 d hd).inv.val.app (op (Proj.basicOpen 𝒮 f))
                (veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
                  ((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
                        (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).unit.app
                      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                        (veroneseModuleGrading 𝒮 𝒨 d))).val.app
                    (op (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)))
                    ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
                        (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)
                        hvf he).symm z))) =
            veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd z) ∧
      -- assertion (2), as the source derives it from (1) at `M = S(nd)`
      (∀ n : ℤ, ∃ E : ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n * d) ≅
          (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
            (ProjectiveSpectrum.Proj.twistingSheaf (veroneseGrading 𝒮 d) n),
        E.hom =
          (associatedModuleSheafVeroneseIso 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d hd).hom ≫
            (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
              (veroneseShiftSheafIso 𝒮 d hd n).hom) ∧
      -- the trailing clause: compatibility of (1) with the multiplication maps
      (∀ (M N : Type u) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
          (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
          (𝒩 : ℤ → AddSubgroup N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩],
        veroneseTensorSquareLeft 𝒮 𝒨 𝒩 d hd = veroneseTensorSquareRight 𝒮 𝒨 𝒩 d hd) ∧
      -- "and hence with (01MO)": `𝒪(nd) ⊗ 𝒪(md) ⟶ 𝒪((n+m)d)` against `𝒪'(n) ⊗ 𝒪'(m) ⟶ 𝒪'(n+m)`
      (∀ n m : ℤ, veroneseTwistMulLeft 𝒮 d hd n m = veroneseTwistMulRight 𝒮 d hd n m) ∧
      -- "and hence with (03GJ)": `𝒪(nd) ⊗ ℱ(md) ⟶ ℱ((n+m)d)` against
      -- `𝒪'(n) ⊗ ℱ'(m) ⟶ ℱ'(n+m)`, for `ℱ = i^*ℱ'`
      (∀ (F' : SheafOfModules.{u}
            ((sheafCompose (Opens.grothendieckTopology
              (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ),
        veroneseTwistSheafMulLeft 𝒮 d hd F' n m = veroneseTwistSheafMulRight 𝒮 d hd F' n m) ∧
      -- "and hence with (03GK)": products of global sections of `𝒪(nd)` and `ℱ(md)`
      (∀ (F' : SheafOfModules.{u}
            ((sheafCompose (Opens.grothendieckTopology
              (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n m : ℤ)
          (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n * d)).val.obj (op ⊤))
          (t : (ProjectiveSpectrum.Proj.twistSheafOfModules 𝒮 (pullbackProjModule 𝒮
            (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F') (m * d)).val.obj (op ⊤))
          (s' : (ProjectiveSpectrum.Proj.twistingSheaf (veroneseGrading 𝒮 d) n).val.obj (op ⊤))
          (t' : (ProjectiveSpectrum.Proj.twistSheafOfModules (veroneseGrading 𝒮 d) F' m).val.obj
            (op ⊤)),
        ((veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)).hom s =
            Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
              (ProjectiveSpectrum.Proj.twistingSheaf (veroneseGrading 𝒮 d) n) ⊤ s' →
        ((veroneseTwistedModuleIso 𝒮 d hd F' m).hom.val.app (op ⊤)).hom t =
            Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
              (ProjectiveSpectrum.Proj.twistSheafOfModules (veroneseGrading 𝒮 d) F' m) ⊤ t' →
        ((veroneseTwistedModuleIso 𝒮 d hd F' (n + m)).hom.val.app (op ⊤)).hom
            (((eqToHom (congrArg (ProjectiveSpectrum.Proj.twistSheafOfModules 𝒮
                (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F'))
                (add_mul n m (d : ℤ)).symm)).val.app (op ⊤)).hom
              (ProjectiveSpectrum.Proj.multiplyHomogeneousSections' 𝒮
                (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d) (veroneseProjIso 𝒮 d hd).hom F')
                (n * d) (m * d) s t)) =
          Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
            (ProjectiveSpectrum.Proj.twistSheafOfModules (veroneseGrading 𝒮 d) F' (n + m)) ⊤
            (ProjectiveSpectrum.Proj.multiplyHomogeneousSections' (veroneseGrading 𝒮 d) F' n m
              s' t')) ∧
      -- "and hence with (01MP)": `S → ⨁ₙ Γ(X, 𝒪_X(n))` against `S' → ⨁ₙ Γ(X', 𝒪_{X'}(n))`
      (letI := (ProjectiveSpectrum.Proj.globalSectionsRingMap 𝒮).gradedRing
       letI := (ProjectiveSpectrum.Proj.globalSectionsRingMap (veroneseGrading 𝒮 d)).gradedRing
       ∀ (n : ℕ) (a : veroneseSubring 𝒮 d),
        (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)
            ((eqToHom (congrArg (ProjectiveSpectrum.Proj.twistingSheaf 𝒮)
              (Nat.cast_mul n d))).val.app (op ⊤)
              (DirectSum.component ℤ ℕ (ProjectiveSpectrum.Proj.twistGlobalSections 𝒮) (n * d)
                ((ProjectiveSpectrum.Proj.globalSectionsRingMap 𝒮).hom (a : S)))) =
          Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
            (ProjectiveSpectrum.Proj.twistingSheaf (veroneseGrading 𝒮 d) n) ⊤
            (DirectSum.component ℤ ℕ
              (ProjectiveSpectrum.Proj.twistGlobalSections (veroneseGrading 𝒮 d)) n
              ((ProjectiveSpectrum.Proj.globalSectionsRingMap (veroneseGrading 𝒮 d)).hom a))) ∧
      -- "and hence with (01MQ)": `M̃ ⊗ 𝒪_X(nd) ⟶ M(nd)~` against `M'~ ⊗ 𝒪_{X'}(n) ⟶ M'(n)~`
      (∀ (M : Type u) [AddCommGroup M] [Module S M] (𝒨 : ℤ → AddSubgroup M)
          [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] (n : ℤ),
        veroneseModuleTwistLeft 𝒮 𝒨 d hd n = veroneseModuleTwistRight 𝒮 𝒨 d hd n) ∧
      -- "and hence with (01MR)": `M → ⨁ₙ Γ(X, M(n)~)` against `M' → ⨁ₙ Γ(X', M'(n)~)`
      (∀ (M : Type v) [AddCommGroup M] [Module S M] (𝒨 : ℤ → AddSubgroup M)
          [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨],
        letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
        ∀ (n : ℤ) (m : veroneseSubmodule 𝒮 𝒨 d),
        (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
            (DirectSum.component ℤ ℤ _ (n * d)
              ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).hom
                (m : M))) =
          pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
            (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
            (DirectSum.component ℤ ℤ _ n
              ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
                (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom m))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  refine ⟨(veroneseProjIso 𝒮 d hd).isIso_hom,
    fun x g => veroneseProjIso_mem_iff 𝒮 d hd x g,
    fun f e he hf => awayι_comp_veroneseProjHom 𝒮 d hd f he hf,
    fun f e he hf => veroneseProjIso_basicOpen 𝒮 d hd f he hf, ?_, ?_, ?_,
    fun n m => veroneseTwistMulCompatibility 𝒮 d hd n m,
    fun F' n m => veroneseTwistSheafMulCompatibility 𝒮 d hd F' n m,
    fun F' n m s t s' t' hs ht =>
      veroneseMultiplyHomogeneousSectionsCompatibility 𝒮 d hd F' n m s t s' t' hs ht,
    fun n a => veroneseGlobalSectionsRingMapCompatibility 𝒮 d hd n a,
    fun M _ _ 𝒨 _ _ n => veroneseModuleTwistCompatibility 𝒮 𝒨 d hd n,
    fun M _ _ 𝒨 _ _ n m => veroneseGlobalSectionsModuleMapCompatibilityAny 𝒮 𝒨 d hd n m⟩
  · intro M _ _ 𝒨 _ _ f e he hf _ z
    exact veroneseAssociatedSheafIso_standardOpen 𝒮 𝒨 d hd f he hf z
  · intro n
    exact ⟨veroneseTwistingSheafIso 𝒮 d hd n, rfl⟩
  · intro M N _ _ _ _ 𝒨 _ _ 𝒩 _ _
    exact veroneseTensorCompatibility 𝒮 𝒨 𝒩 d hd

end Stacks.Veronese

end
