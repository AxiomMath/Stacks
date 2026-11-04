module

public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparisonEpi
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Algebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change of the extension algebra of a finite étale cover

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement carries
depth at least two, and `π : V ⟶ U` a finite étale cover.  The extension algebra of the cover
is `𝓑 = (π ≫ j)_* 𝒪_V`, which is quasi-coherent by
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtaleAlgebra_isCoherent`.  This file proves
that `𝓑` commutes with flat base change: for a flat `g : X' ⟶ X` and the base changes `j'` of
`j` and `π'` of `π`, the pulled-back algebra `g⁻¹𝓑 ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is canonically the
extension algebra `(π' ≫ j')_* 𝒪_{V'}` of the base-changed cover, compatibly with the
base-change morphism.

## Main definitions

* `Stacks.FundamentalGroup.algebraPullbackOfFlat` is the extension-of-scalars datum
  `Stacks.RelativeSpec.AlgebraPullback` of [Stacks, Tag 01LS] for a flat morphism, built from
  `Stacks.AffineAlgebraEquivalence.algebraPullback`.  The datum itself, and the
  relative-spectrum situation `Stacks.RelativeSpec.AlgebraPullback.situation` it defines on the
  new base, are taken from `StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChange`; this file
  adds the two projections of the situation.

## Main results

* `Stacks.FundamentalGroup.isIso_baseChangeAlgebraHom` — the base-change clause of
  [Stacks, Tag 01SA] along a flat morphism:  for `W` quasi-compact and quasi-separated over
  `X`, the canonical comparison `g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'} ⟶ f'_* 𝒪_{W ×_X X'}` is an
  isomorphism.
* `Stacks.FundamentalGroup.nonempty_algebraPullback` — the existence clause of
  [Stacks, Tag 01LS] for a flat morphism of bases.
* `Stacks.FundamentalGroup.exists_algebraIso_pushforwardAlgebra_of_isPushout` — an algebra
  sheaf on `X'` exhibited as the extension of scalars of `f_* 𝒪_V` along a flat `g`, for `f`
  quasi-compact and quasi-separated, is canonically the direct image of the structure sheaf of
  any scheme over `X'` isomorphic to `V ×_X X'`.
* `Stacks.FundamentalGroup.algebraHom_ext_of_isPushout` and
  `Stacks.FundamentalGroup.algebraIso_eq_of_isPushout` — a morphism out of an extension of
  scalars is determined by its restriction along the canonical map, so the comparison above is
  the *unique* isomorphism with the stated compatibility.
* `Stacks.FundamentalGroup.exists_extendedEtaleAlgebraComparison` — the same for the extension
  algebra of a finite étale cover, for an arbitrary extension of scalars of it;
  `Stacks.FundamentalGroup.exists_extendedEtaleAlgebraComparison_algebraPullbackOfFlat` is its
  instance at `Stacks.FundamentalGroup.extendedEtaleAlgebraPullback`, which is the shape in
  which [Stacks, Tag 0EY6] states the clause.

## Implementation notes

The whole content is the unconditional epimorphism
`Stacks.FundamentalGroup.epi_algebraPullbackModuleComparison`, through
`Stacks.FundamentalGroup.flatBaseChange_algebraPullback`:  that theorem says
`(π ≫ j)'_* 𝒪_{V'}` sits in the extension-of-scalars pushout square, and the datum of an
`AlgebraPullback` says the same of its own algebra, so the comparison is
`CategoryTheory.IsPushout.isoIsPushout` for two pushouts of one span, lifted to `Under` by
`CategoryTheory.Under.isoMk`.  Quasi-compactness of `π ≫ j` — the hypothesis of
`flatBaseChange_algebraPullback` which the statement of the tag does not list — is *automatic*
here: an open immersion into a locally Noetherian scheme is quasi-compact
([Stacks, Tag 01OX], a Mathlib instance), a finite morphism is quasi-compact, and both
properties are stable under composition.  Without `IsLocallyNoetherian X` the instance does not
synthesize, so the hypothesis is doing work.

The transport along the comparison of covers is `Stacks.AffineAlgebraEquivalence`'s
contravariant action `pushforwardAlgebraMap`, made into an isomorphism from
`pushforwardAlgebraMap_comp` and `pushforwardAlgebraMap_id` rather than through
`pushforwardAlgebraFunctor`, so that the morphism appearing in the conclusion is syntactically
`pushforwardAlgebraMap e.hom`, which is what the statement of [Stacks, Tag 0EY6] names.

**No `@[stacks]` attribute is placed in this file.**  Tag 0EY6 has no attribute site anywhere
in this library, by the policy recorded in the docstrings of
`Stacks.FundamentalGroup.extendedEtaleDepth_flatBaseChange` and of
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtaleSituation`:  the tag's flat-base-change
part has SEVEN clauses, and the three concerning the relative *spectrum* of the extension
algebra are not proved here (two of them now are, in `FlatBaseChange/SpectrumComparison.lean`).

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.RelativeSpec

/-- The base of the relative-spectrum situation of an algebra pullback along `g : S' ⟶ s.base`
is `S'`. -/
@[simp]
public theorem AlgebraPullback.situation_base {s : RelativeSpecSituation.{u}} {S' : Scheme.{u}}
    {g : S' ⟶ s.base} (d : AlgebraPullback s g) : d.situation.base = S' :=
  rfl

/-- The algebra of the relative-spectrum situation of an algebra pullback `d` is the pulled-back
algebra `d.algebra`. -/
@[simp]
public theorem AlgebraPullback.situation_algebra {s : RelativeSpecSituation.{u}}
    {S' : Scheme.{u}} {g : S' ⟶ s.base} (d : AlgebraPullback s g) :
    d.situation.algebra = d.algebra :=
  rfl

end Stacks.RelativeSpec

namespace Stacks.FundamentalGroup

/-! ### The base-change comparison of algebras is invertible -/

/-- **The canonical base-change comparison of algebras is an isomorphism**, for a flat
`g : X' ⟶ X` and a quasi-compact quasi-separated scheme `W` over `X`:  the base change of
`f_* 𝒪_W` is `f'_* 𝒪_{W ×_X X'}`.  This is
`Stacks.FundamentalGroup.isIso_baseChangeAlgebraHom_of_epi_comparison` composed with the
unconditional `Stacks.FundamentalGroup.epi_algebraPullbackModuleComparison`, and it is the
base-change clause of [Stacks, Tag 01SA] along a flat morphism.

The implementation notes of the module defining `baseChangeAlgebraHom` say that inverting it
needs both quasi-coherence of the algebra pullback and the representability of the relative
spectrum over an arbitrary base.  Both halves of that are now out of date:  quasi-coherence is
`isQuasicoherent_algebraPullback`, and this proof uses no representability at all. -/
@[sga "3 I 6.6.1" "special case", sga "6 0 2.9" "Structure-sheaf clause"]
public theorem isIso_baseChangeAlgebraHom {X X' : Scheme.{u}} (g : X' ⟶ X) [Flat g]
    (W : Over X) [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    IsIso (baseChangeAlgebraHom g W) :=
  isIso_baseChangeAlgebraHom_of_epi_comparison g W
    (epi_algebraPullbackModuleComparison g (pushforwardAlgebra W.hom))

/-! ### The existence clause of Tag 01LS along a flat morphism -/

/-- **Extension of scalars of a quasi-coherent algebra along a flat morphism of bases**, as the
datum `Stacks.RelativeSpec.AlgebraPullback`.  The algebra is
`Stacks.AffineAlgebraEquivalence.algebraPullback`, whose pushout square is
`Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout` and whose quasi-coherence is
`Stacks.FundamentalGroup.isQuasicoherent_algebraPullback`. -/
public def algebraPullbackOfFlat (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}}
    (g : S' ⟶ s.base) [Flat g] : AlgebraPullback s g where
  algebra := (algebraPullback g).obj s.algebra
  map := (algebraPullbackMap g).app s.algebra
  isPushout := algebraPullback_isPushout g s.algebra
  isQuasicoherent := isQuasicoherent_algebraPullback g s.algebra

/-- **The existence clause of [Stacks, Tag 01LS] for a flat morphism of bases.**  Extension of
scalars of a quasi-coherent algebra sheaf along a flat morphism exists and is quasi-coherent.
(For an arbitrary morphism this is the `algebraPullback_isQuasicoherent` clause of
[Stacks, Tag 01SA], which is not proved in this library.) -/
public theorem nonempty_algebraPullback (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}}
    (g : S' ⟶ s.base) [Flat g] : Nonempty (AlgebraPullback s g) :=
  ⟨algebraPullbackOfFlat s g⟩

/-- **Extension of scalars of the extension algebra of a finite étale cover along a flat
morphism.**  This is `algebraPullbackOfFlat` at the situation
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtaleSituation`, named separately because
`Flat g` is a class and the base of that situation is only *definitionally* the scheme `X` that
`g` maps to:  instance search is syntactic, so `algebraPullbackOfFlat` applied to the situation
cannot find the ambient `Flat g`, while here the instance is found at `g`'s own type and only
the resulting *type* is unified with the situation's base. -/
public def extendedEtaleAlgebraPullback {U X V X' : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))
    (g : X' ⟶ X) [Flat g] :
    AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g where
  algebra := (algebraPullback g).obj (pushforwardAlgebra (π ≫ j))
  map := (algebraPullbackMap g).app (pushforwardAlgebra (π ≫ j))
  isPushout := algebraPullback_isPushout g (pushforwardAlgebra (π ≫ j))
  isQuasicoherent :=
    have : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent :=
      (ExtendedEtaleFold.extendedEtaleSituation j π hdepth).isQuasicoherent
    isQuasicoherent_algebraPullback g (pushforwardAlgebra (π ≫ j))

/-! ### Flat base change of a direct image, read off two pushout squares -/

/-- **A morphism out of an extension of scalars is determined by its restriction along the
canonical map.**  If `m : g⁻¹A ⟶ B` exhibits the algebra sheaf `B` as the extension of scalars
of `A` along `g`, two morphisms of algebra sheaves out of `B` which agree after `m` are equal:
their structure-morphism legs agree because every morphism of algebra sheaves commutes with the
structure morphisms. -/
public theorem algebraHom_ext_of_isPushout {X X' : Scheme.{u}} {g : X' ⟶ X}
    {A : AlgebraSheaf X} {B C : AlgebraSheaf X'}
    {m : (TopCat.Sheaf.pullback CommRingCat g.base).obj A.right ⟶ B.right}
    (hm : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom)
      (inverseImageStructureMap g) m B.hom)
    (φ ψ : B ⟶ C) (h : m ≫ φ.right = m ≫ ψ.right) : φ = ψ :=
  Under.UnderMorphism.ext (hm.hom_ext h ((Under.w φ).trans (Under.w ψ).symm))

/-- **The comparison of `exists_algebraIso_pushforwardAlgebra_of_isPushout` is unique.**  Two
isomorphisms out of an extension of scalars which carry the canonical map to the same morphism
are equal, so the existential statement of [Stacks, Tag 0EY6] determines its witness and is not
a weak existence. -/
public theorem algebraIso_eq_of_isPushout {X X' : Scheme.{u}} {g : X' ⟶ X}
    {A : AlgebraSheaf X} {B C : AlgebraSheaf X'}
    {m : (TopCat.Sheaf.pullback CommRingCat g.base).obj A.right ⟶ B.right}
    (hm : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom)
      (inverseImageStructureMap g) m B.hom)
    {n : (TopCat.Sheaf.pullback CommRingCat g.base).obj A.right ⟶ C.right}
    (i₁ i₂ : B ≅ C) (h₁ : m ≫ i₁.hom.right = n) (h₂ : m ≫ i₂.hom.right = n) : i₁ = i₂ :=
  Iso.ext (algebraHom_ext_of_isPushout hm i₁.hom i₂.hom (h₁.trans h₂.symm))

/-- **An extension of scalars of `f_* 𝒪_V` along a flat morphism is a direct image.**  Let
`f : V ⟶ X` be quasi-compact and quasi-separated, let `g : X' ⟶ X` be flat, and let `B` be a
sheaf of commutative `𝒪_{X'}`-algebras exhibited by `m` as the extension of scalars
`g⁻¹(f_* 𝒪_V) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`.  Then for every scheme `W'` over `X'` together with an
isomorphism `e : W' ≅ V ×_X X'` over `X'` there is an isomorphism of algebra sheaves
`B ≅ (W' ⟶ X')_* 𝒪_{W'}` carrying `m` to the base-change morphism transported along `e`.

Both `B` and `f'_* 𝒪_{V ×_X X'}` sit in the extension-of-scalars pushout square — the latter by
`flatBaseChange_algebraPullback` — so they are identified by
`CategoryTheory.IsPushout.isoIsPushout`. -/
public theorem exists_algebraIso_pushforwardAlgebra_of_isPushout {V X X' : Scheme.{u}}
    (f : V ⟶ X) [QuasiCompact f] [QuasiSeparated f] (g : X' ⟶ X) [Flat g]
    {B : AlgebraSheaf X'}
    (m : (TopCat.Sheaf.pullback CommRingCat g.base).obj (pushforwardAlgebra f).right ⟶ B.right)
    (hm : IsPushout
      ((TopCat.Sheaf.pullback CommRingCat g.base).map (pushforwardAlgebra f).hom)
      (inverseImageStructureMap g) m B.hom)
    {W' : Over X'} (e : W' ≅ (Over.pullback g).obj (Over.mk f)) :
    ∃ i : B ≅ pushforwardAlgebra W'.hom,
      m ≫ i.hom.right =
        pushforwardBaseChangeMap g (Over.mk f) ≫ (pushforwardAlgebraMap e.hom).right := by
  have h := flatBaseChange_algebraPullback f g
  let φ := IsPushout.isoIsPushout _ _ hm h
  have hinl : m ≫ φ.hom = pushforwardBaseChangeMap g (Over.mk f) :=
    IsPushout.inl_isoIsPushout_hom _ _ hm h
  have hinr : B.hom ≫ φ.hom =
      (pushforwardAlgebra ((Over.pullback g).obj (Over.mk f)).hom).hom :=
    IsPushout.inr_isoIsPushout_hom _ _ hm h
  have key : ∀ {a b : Over X'} (p : a ≅ b),
      pushforwardAlgebraMap p.hom ≫ pushforwardAlgebraMap p.inv = 𝟙 _ := fun p => by
    rw [← pushforwardAlgebraMap_comp, p.inv_hom_id, pushforwardAlgebraMap_id]
  let ψ : pushforwardAlgebra ((Over.pullback g).obj (Over.mk f)).hom ≅
      pushforwardAlgebra W'.hom :=
    { hom := pushforwardAlgebraMap e.hom
      inv := pushforwardAlgebraMap e.inv
      hom_inv_id := key e
      inv_hom_id := key e.symm }
  refine ⟨Under.isoMk φ hinr ≪≫ ψ, ?_⟩
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hinl)

/-! ### The flat-base-change clause of Tag 0EY6 for the extension algebra -/

/-- **[Stacks, Tag 0EY6], flat base change of the extension algebra.**  Let `X` be locally
Noetherian, `j : U ⟶ X` an open immersion whose complement carries depth at least two and
`π : V ⟶ U` a finite étale cover, and let `g : X' ⟶ X` be flat with `j'` the base change of `j`
and `π'` the base change of `π`.  Then every extension of scalars of the extension algebra
`𝓑 = (π ≫ j)_* 𝒪_V` along `g` is canonically isomorphic to the extension algebra
`(π' ≫ j')_* 𝒪_{V'}` of the base-changed cover, by an isomorphism carrying the canonical map
`g⁻¹𝓑 ⟶ g⁺𝓑` to the base-change morphism transported along the Cartesian comparison of
covers.

This is stated for an arbitrary `Stacks.RelativeSpec.AlgebraPullback`, hence in particular for
any choice of one;  `exists_extendedEtaleAlgebraComparison_algebraPullbackOfFlat` is the
instance at `algebraPullbackOfFlat`. -/
@[stacks 0EY6 "flat_base_change"]
public theorem exists_extendedEtaleAlgebraComparison {U X V U' X' V' : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (g : X' ⟶ X) [Flat g]
    (j' : U' ⟶ X') [IsOpenImmersion j'] (gU : U' ⟶ U)
    (π' : V' ⟶ U') [IsFinite π'] [Etale π'] (gV : V' ⟶ V)
    (hj : IsPullback j' gU g j)
    (hπ : IsPullback π' gV gU π)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    let hdepth' := extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth
    let e : Over.mk (π' ≫ j') ≅ (Over.pullback g).obj (Over.mk (π ≫ j)) :=
      Over.isoMk (hπ.paste_horiz hj).flip.isoPullback (by simp)
    ∃ i : d.algebra ≅
        (ExtendedEtaleFold.extendedEtaleSituation j' π' hdepth').algebra,
      d.map ≫ i.hom.right =
        pushforwardBaseChangeMap g (Over.mk (π ≫ j)) ≫
          (pushforwardAlgebraMap e.hom).right := by
  intro hdepth' e
  exact exists_algebraIso_pushforwardAlgebra_of_isPushout (π ≫ j) g d.map d.isPushout e

/-- **[Stacks, Tag 0EY6], flat base change of the extension algebra**, at the extension of
scalars `algebraPullbackOfFlat` supplied by `Stacks.AffineAlgebraEquivalence.algebraPullback`.
This is the statement of the clause;  `exists_extendedEtaleAlgebraComparison` proves it for an
arbitrary extension of scalars. -/
public theorem exists_extendedEtaleAlgebraComparison_algebraPullbackOfFlat
    {U X V U' X' V' : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (g : X' ⟶ X) [Flat g]
    (j' : U' ⟶ X') [IsOpenImmersion j'] (gU : U' ⟶ U)
    (π' : V' ⟶ U') [IsFinite π'] [Etale π'] (gV : V' ⟶ V)
    (hj : IsPullback j' gU g j)
    (hπ : IsPullback π' gV gU π)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) :
    let hdepth' := extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth
    let d := extendedEtaleAlgebraPullback j π hdepth g
    let e : Over.mk (π' ≫ j') ≅ (Over.pullback g).obj (Over.mk (π ≫ j)) :=
      Over.isoMk (hπ.paste_horiz hj).flip.isoPullback (by simp)
    ∃ i : d.algebra ≅
        (ExtendedEtaleFold.extendedEtaleSituation j' π' hdepth').algebra,
      d.map ≫ i.hom.right =
        pushforwardBaseChangeMap g (Over.mk (π ≫ j)) ≫
          (pushforwardAlgebraMap e.hom).right := by
  intro hdepth' d e
  exact exists_extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d

end Stacks.FundamentalGroup

end
