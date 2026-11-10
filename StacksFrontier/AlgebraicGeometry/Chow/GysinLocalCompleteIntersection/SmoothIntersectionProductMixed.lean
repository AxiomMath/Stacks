module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward
public import
  StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalCycle
public import
  StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DiagonalUnit

/-!
# The Gysin map and the intersection product on smooth schemes of arbitrary dimension

Let `k` be a field and let `f : X ⟶ Y` be a morphism of schemes smooth over `k`. Stacks 0FFB and
Stacks 0FFC assert

* `f^!(α · β) = f^!α · f^!β`, and
* if `f` is proper, `f_*(α · f^!β) = f_*α · β` (the projection formula),

with no assumption that `X` or `Y` is equidimensional or quasi-compact. Their proofs reduce to
the pieces of `X` and `Y` of constant dimension, where the source's argument applies to any class
with the properties of Stacks 0FF6 and Stacks 0FF7
(`Stacks.Chow.BivariantClass.capTargetHom_selfIntersectionProduct`). This file carries out the
reduction.

A scheme `X` smooth over `k` is the disjoint union `X = ∐_d X_d` of its open and closed parts
`X_d` of dimension `d` (Stacks 02NM, `Stacks.WeilCohomology.dimPart`), and the intersection
product of Stacks 0FC0 is formed part by part: "in general we can decompose into the parts lying
over the open and closed subschemes of `X` where `X` has a given dimension". On `X_d` the product
`CH_n(X_d) × CH_m(X_d) ⟶ CH_{n+m-d}(X_d)` changes the dimension by `d`, which varies with the
part, so the product is graded by codimension:

  `CH^i(X) = ∏_d CH_{d-i}(X_d)`,   `(α · β)_d = α_d · β_d ∈ CH_{d-i-j}(X_d)`,

a product rather than a direct sum since `X` need not be quasi-compact. Chow groups graded by
dimension decompose the same way, `CH_n(X) = ∏_d CH_n(X_d)`, and the product of
`α ∈ CH_n(X)` with `β ∈ CH^j(X)` is the class in `CH_{n-j}(X)` whose restriction to `X_d` is
`α|_{X_d} · β_d`.

Writing `X_{d,e} = X_d ∩ f⁻¹(Y_e)`, the scheme `X_d` is the disjoint union of the open and closed
`X_{d,e}`, and `f` restricts to `f_{d,e} : X_{d,e} ⟶ Y_e`, a morphism between schemes smooth over
`k` of dimensions `d` and `e`. The Gysin map `f^!` of `f` (Stacks 0FF3) restricts to a class of
`A^{e-d}(X_{d,e} ⟶ Y_e)`, which carries `CH_{e-i}(Y_e)` to `CH_{d-i}(X_{d,e})`, and
`f^! : CH^i(Y) ⟶ CH^i(X)` is the map whose restriction to each `X_{d,e}` is `β ↦ f^! β_e`.

**Stacks 0FFB.** Both sides of `f^!(α · β) = f^!α · f^!β` are compared on each `X_{d,e}`. There
the left side is `f^!(α_e · β_e)`; the right side is the restriction to the open subscheme
`X_{d,e}` of a product on `X_d`, which is the product of the restrictions, restriction being flat
pullback in relative dimension zero, under which the product is multiplicative
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_flatPullbackMul`). The two agree by the
source's argument, the restriction of `f^!` to `X_{d,e}` satisfying Stacks 0FF6 and Stacks 0FF7
there.

**Stacks 0FFC.** Both sides of `f_*(α · f^!β) = f_*α · β` are compared on each `Y_e`, where
proper pushforward commutes with restriction to the open subscheme `Y_e` (Stacks 02RG for an open
immersion). Over `Y_e` the scheme `f⁻¹(Y_e) = ∐_d X_{d,e}` may have infinitely many nonempty
parts, so `f_*` from it is not a finite sum of the pushforwards from the parts, and the
equidimensional statements on the parts cannot be added up. The source's own argument is local
and is carried out on `f⁻¹(Y_e)` instead: by Stacks 0FC2 write `β_e = c ∩ [Y_e]_e` with
`c ∈ A^j(Y_e)`, so that `γ · β_e = c ∩ γ` on `Y_e`; then `c ∩ f_*α = f_*(res(c) ∩ α)`, and
`α · f^!β = res(c) ∩ α` holds on `f⁻¹(Y_e)` because it holds on each part `X_{d,e}`, where
`f^!β_e = res(c) ∩ [X_{d,e}]_d` by Stacks 0FF6 and Stacks 0FF7, and capping with
`res(c)` commutes with restriction to the parts.

## Main definitions

* `Stacks.Chow.codimensionChowGroup` — `CH^i(X) = ∏_d CH_{d-i}(X_d)`.
* `Stacks.Chow.chowGroupDimPartEquiv` — `CH_n(X) = ∏_d CH_n(X_d)`.
* `Stacks.Chow.codimensionIntersectionProduct` — the intersection product
  `CH^i(X) × CH^j(X) ⟶ CH^{i+j}(X)` of Stacks 0FC0.
* `Stacks.Chow.dimensionCodimensionIntersectionProduct` — the intersection product
  `CH_n(X) × CH^j(X) ⟶ CH_{n-j}(X)`.
* `Stacks.Chow.dimPartPiece`, `Stacks.Chow.dimPartPieceHom` — the pieces `X_{d,e}` and the
  restrictions `f_{d,e} : X_{d,e} ⟶ Y_e` of `f`.
* `Stacks.Chow.dimPartPieceGysinClass` — the Gysin map of `f`, restricted to `X_{d,e}` and `Y_e`,
  in its degree `e - d` there.
* `Stacks.Chow.codimensionGysin` — the Gysin map `f^! : CH^i(Y) ⟶ CH^i(X)`.

## Main results

* `Stacks.Chow.codimensionGysin_codimensionIntersectionProduct` — **Stacks 0FFB**,
  `f^!(α · β) = f^!α · f^!β`.
* `Stacks.Chow.properChowPushforward_dimensionCodimensionIntersectionProduct_codimensionGysin`
  — **Stacks 0FFC**, `f_*(α · f^!β) = f_*α · β` for `f` proper.
* `Stacks.Chow.dimPartPieceGysinClass_bivariantCommute`,
  `Stacks.Chow.dimPartPieceGysinClass_capTargetHom_fundamentalChowClass` — Stacks 0FF6 and
  Stacks 0FF7 at `Y' = Y_e` for the Gysin map of `f` restricted to `X_{d,e}`:
  `f^![Y_e]_e = [X_{d,e}]_d`.
* `Stacks.Chow.smoothGysinChow_fundamentalChowClass` — Stacks 0FF7 at `Y' = Y` for a morphism of
  schemes smooth over `k` of constant dimensions `d` and `e`: `f^![Y]_e = [X]_d`.
* `Stacks.Chow.chowGroupRestrict_selfIntersectionProduct_canonical` — the intersection product
  commutes with restriction to an open subscheme.
* `Stacks.Chow.chowGroupRestrict_chowCohomologyCap_restrictionOfEq` — capping with a restricted
  class of Chow cohomology commutes with restriction to an open subscheme.
* `Stacks.Chow.BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq` —
  `F ∩ (c ∩ [Y]_e) = res(c) ∩ [X]_{e-q}` for a class `F` commuting with `c` and carrying `[Y]_e`
  to `[X]_{e-q}`.

## Implementation notes

The Gysin map `f^!` of Stacks 0FF3 is an element of `A^*(X ⟶ Y)^∧ = ∏_p A^p(X ⟶ Y)`
(Stacks 0FE0) whose degree is not constant: on the open subscheme `X_{d,e}` of `X` it is
concentrated in degree `e - d`. The map `Stacks.Chow.codimensionGysin` is `f^!` itself
(`Stacks.Chow.lciGysinMap` of `f`), acting part by part: its restriction to `X_{d,e}` is cap
product with the degree `e - d` part of `f^!`, restricted along `Y_e ⟶ Y` (Stacks 0F9Z) and then
to the open subscheme `X_{d,e}` of `X ×_Y Y_e` (`Stacks.Chow.dimPartPieceGysinClass`), applied
to `β_e` (`Stacks.Chow.chowGroupRestrict_codimensionGysin`). That this restriction is the Gysin
map of `f_{d,e}` is not used; Stacks 0FF6 and Stacks 0FF7 are proved for it directly, from those
of `f^!`.

The source states Stacks 0FFB for `α, β ∈ CH_*(Y)` graded by dimension. A class of `CH_n(Y)` has
codimension `e - n` on `Y_e`, which varies with `e`, so neither it nor its image under `f^!` (of
degree `e - d` on `X_{d,e}`) is homogeneous for either grading once `Y` has parts of several
dimensions. Both sides of each identity are determined by their restrictions to the pieces
`X_{d,e}`, where they depend only on the restrictions of `α` and `β` to `Y_e`; there the
statement for dimension-graded classes is the codimension-graded one, which is what is proved.

The schemes are only assumed smooth over `k`, as in the source. The diagonal `Δ : X ⟶ X ×_k X`
is then an immersion, not necessarily closed, and its Gysin class (Stacks 0FBR,
`Stacks.Chow.diagonalGysinClass`) is formed on the open subscheme of `X ×_k X` in which `Δ` is
closed, so neither it nor the parts `X_d` need `X` separated.

The inputs of the argument on each piece are theorems: Stacks 0FF7 at `Y' = Y_e` is
`Stacks.Chow.dimPartPieceGysinClass_capTargetHom_fundamentalChowClass`, Stacks 0FF6 is
`Stacks.Chow.dimPartPieceGysinClass_bivariantCommute`, and Stacks 0FC2 for the canonical classes
of the diagonals is `Stacks.WeilCohomology.capFundamentalClassSurjective` and
`Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`, with the symmetry of the
product `Stacks.WeilCohomology.canonicalDiagonalClassFamily_isSymmetric`.

The pieces `X_d`, `X_{d,e}` are indexed by `ULift ℕ` where a decomposition of Chow groups needs an
index type in the universe of the schemes (`Stacks.Chow.chowGroupClopenRestrictEquiv`).

## References

* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Section 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A decomposition into open and closed subschemes, reindexed along an equivalence of index
types and presented by the inclusions of its pieces, is again one. -/
theorem IsClopenDecomposition.opensRange_ι_equiv {X : Scheme.{u}} {I J : Type*}
    {U : I → X.Opens} (h : IsClopenDecomposition U) (e : J ≃ I) :
    IsClopenDecomposition fun j ↦ (U (e j)).ι.opensRange where
  disjoint i j hij := by
    simp only [Scheme.Opens.opensRange_ι]
    exact h.disjoint _ _ (e.injective.ne hij)
  iSup_eq_top := by
    simp only [Scheme.Opens.opensRange_ι]
    rw [e.iSup_comp (g := U)]
    exact h.iSup_eq_top


section CapRestrict

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
  {Y W V : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (p : ℤ)

/-- **The cap product with a restricted class of Chow cohomology, read through the cap of the
class itself.** For `c ∈ A^p(Y)` and `g : W ⟶ Y`, `res(c) ∩ γ` is `c ∩ γ` formed at the test
scheme `g` and read on `W` through `Y ×_Y W ≅ W`. -/
theorem chowCohomologyCap_restrictionOfEq (g : W ⟶ Y) [LocallyOfFiniteType g]
    (hg : g ≫ sY = sW) (c : chowCohomologyComponent C G sY p) (k : ℤ) (γ : chowGroup C sW k) :
    chowCohomologyCap C G sW p (chowCohomologyRestrictionOfEq C sW sY hg G hgys p c) k γ =
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) g ≫ sY) sW (identityBaseChangeIso g).hom
        (by rw [← hg]; exact identityBaseChangeIso_hom_comp_base C sY g) (k - p)
        (c.cap g k (chowGroupCongr C hg.symm k γ)) := by
  subst hg
  set α := chowGroupCongr C (Category.id_comp (g ≫ sY)).symm k γ
  have hres := chowCohomologyRestriction_cap C G sY g p hgys c (𝟙 W) k α
  have hL : chowCohomologyCap C G (g ≫ sY) p
        (chowCohomologyRestrictionOfEq C (g ≫ sY) sY rfl G hgys p c) k γ =
      chowPushforwardOfIso C (pullback.fst (𝟙 W) (𝟙 W) ≫ (g ≫ sY)) (g ≫ sY)
        (pullback.fst (𝟙 W) (𝟙 W)) rfl (k - p)
        ((chowCohomologyRestriction C G sY g p hgys c).cap (𝟙 W) k α) := rfl
  have hfs : pullback.fst (𝟙 W) (𝟙 W) = (identityBaseChangeIso (𝟙 W)).hom := by
    rw [asIso_hom, ← Category.comp_id (pullback.fst (𝟙 W) (𝟙 W)), pullback.condition,
      Category.comp_id]
  have key : ∀ (m : W ⟶ Y) [LocallyOfFiniteType m] (hm : m = g)
      (x : chowGroup C (m ≫ sY) k), x ≍ γ →
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) m ≫ sY) (g ≫ sY) (identityBaseChangeIso m).hom
          (by rw [← hm]; exact identityBaseChangeIso_hom_comp_base C sY m) (k - p)
          (c.cap m k x) =
        chowPushforwardOfIso C (pullback.fst (𝟙 Y) g ≫ sY) (g ≫ sY)
          (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sY g) (k - p)
          (c.cap g k (chowGroupCongr C rfl k γ)) := by
    intro m _ hm x hx
    subst hm
    cases hx
    rfl
  rw [hL, chowPushforwardOfIso_congr_apply C _ _ _ _ hfs rfl (by rw [← hfs])]
  refine eq_of_heq ((chowPushforwardOfIso_heq _ _ _ rfl (Category.id_comp (g ≫ sY)).symm rfl
    HEq.rfl).trans ((heq_of_eq hres).trans (HEq.trans ?_ (heq_of_eq
      (key (𝟙 W ≫ g) (Category.id_comp g)
        (chowGroupCongr C (Category.assoc (𝟙 W) g sY).symm k α)
        ((chowGroupCongr_heq C _ k α).trans (chowGroupCongr_heq C _ k γ)))))))
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.id_comp (g ≫ sY)) rfl HEq.rfl

/-- **Restricting the cap product with a restricted class of Chow cohomology along an open
immersion.** For `c ∈ A^p(Y)`, `g : W ⟶ Y` and an open immersion `j : V ⟶ W`,

  `(res_g(c) ∩ γ)|_V = res_{j ≫ g}(c) ∩ γ|_V`.

Both sides are `c ∩ γ` formed at a test scheme over `Y` and read on `V`
(`Stacks.Chow.chowCohomologyCap_restrictionOfEq`), and the cap operation of `c` commutes with
restricting the test scheme along an open immersion
(`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`). -/
theorem chowGroupRestrict_chowCohomologyCap_restrictionOfEq (g : W ⟶ Y) [LocallyOfFiniteType g]
    (hg : g ≫ sY = sW) (j : V ⟶ W) [IsOpenImmersion j] (hj : j ≫ sW = sV)
    (c : chowCohomologyComponent C G sY p) (k : ℤ)
    (γ : chowGroup C sW k) :
    chowGroupRestrict C sW sV j hj (k - p)
        (chowCohomologyCap C G sW p (chowCohomologyRestrictionOfEq C sW sY hg G hgys p c) k γ) =
      chowCohomologyCap C G sV p
        (chowCohomologyRestrictionOfEq C sV sY (show (j ≫ g) ≫ sY = sV by
          rw [Category.assoc, hg, hj]) G hgys p c) k (chowGroupRestrict C sW sV j hj k γ) := by
  rw [chowCohomologyCap_restrictionOfEq, chowCohomologyCap_restrictionOfEq]
  set eW := identityBaseChangeIso g with heW
  set eV := identityBaseChangeIso (j ≫ g) with heV
  set v' : pullback (𝟙 Y) (j ≫ g) ⟶ pullback (𝟙 Y) g := eV.hom ≫ j ≫ eW.inv with hv'
  have hsq : IsPullback (pullback.snd (𝟙 Y) (j ≫ g)) v' j (pullback.snd (𝟙 Y) g) :=
    IsPullback.of_horiz_isIso ⟨by simp [hv', heV, heW]⟩
  have hfst : v' ≫ pullback.fst (𝟙 Y) g = pullback.fst (𝟙 Y) (j ≫ g) := by
    rw [fst_eq_identityBaseChangeIso_hom g, fst_eq_identityBaseChangeIso_hom (j ≫ g), hv']
    simp only [Category.assoc, Iso.inv_hom_id_assoc, heW, heV]
  have hcap := BivariantClass.cap_chowGroupRestrict C G sY sY (𝟙 Y) (Category.id_comp sY) p c g
    j (j ≫ g) rfl v' hsq hfst k (by rw [Category.assoc])
    (by rw [← Category.assoc, hfst]) (chowGroupCongr C hg.symm k γ)
  rw [chowPushforwardOfIso_eq_chowGroupRestrict C _ _ eW.hom _ eW.inv eW.inv_hom_id,
    chowGroupRestrict_comp,
    chowPushforwardOfIso_eq_chowGroupRestrict C _ _ eV.hom _ eV.inv eV.inv_hom_id,
    chowGroupRestrict_congr C (pullback.fst (𝟙 Y) g ≫ sY) sV (j ≫ eW.inv) _ (k - p)
      (eV.inv ≫ v') (by simp [hv'])
      (by rw [fst_eq_identityBaseChangeIso_hom g]; simp [hv', heW, hg, hj])]
  rw [← chowGroupRestrict_comp (sU := pullback.fst (𝟙 Y) (j ≫ g) ≫ sY) (j := v')
    (hj := by rw [← Category.assoc, hfst]) (i := eV.inv)
    (hi := by rw [fst_eq_identityBaseChangeIso_hom (j ≫ g)]; simp [heV, hg, hj]), hcap]
  congr 2
  subst hg hj
  exact eq_of_heq ((chowGroupRestrict_heq_congr C _ _ _ j j _ rfl rfl k γ).trans
    (chowGroupCongr_heq C _ k _).symm)

/-- **Stacks 0FA2 and Stacks 0FF7 on a fundamental class.** If `F ∈ A^q(W ⟶ Y)` commutes with
`c ∈ A^p(Y)` in the sense of Stacks 0FA2 and `F ∩ [Y]_e = [W]_{e-q}`, then

  `F ∩ (c ∩ [Y]_e) = res(c) ∩ [W]_d`   for `d = e - q`,

by `Stacks.Chow.BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute` at `[Y]_e`. -/
theorem BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq {g : W ⟶ Y}
    [LocallyOfFiniteType g] (hg : g ≫ sY = sW) (q : ℤ)
    (F : BivariantClass C G sW sY g hg q) (c : chowCohomologyComponent C G sY p)
    (hcomm : BivariantCommute C G sY g (𝟙 Y) q p (bivariantClassCongrBase C G g hg.symm rfl q F)
      (bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl p c))
    (e : ℤ) (hF : F.capTargetHom C G sW sY g hg q e (fundamentalChowClass C sY e) =
      fundamentalChowClass C sW (e - q)) {d : ℤ} (hd : e - q = d) :
    F.capTargetHom C G sW sY g hg q (e - p) (chowCohomologyCapFundamentalClass C G sY e p c) ≍
      chowCohomologyCapFundamentalClass C G sW d p
        (chowCohomologyRestrictionOfEq C sW sY hg G hgys p c) := by
  subst hd
  rw [← chowCohomologyCap_fundamentalChowClass C G sY p c e,
    ← chowCohomologyCap_fundamentalChowClass C G sW p _ (e - q), BivariantClass.capTargetHom_apply,
    BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute C G hgys sW sY g hg p q F c
      hcomm e (fundamentalChowClass C sY e), ← BivariantClass.capTargetHom_apply, hF]
  exact chowGroupDegreeEquiv_heq _ _ _ _

end CapRestrict

section CapTarget

/-- A bivariant class caps classes of degrees written differently, and heterogeneously equal,
to heterogeneously equal classes. -/
theorem BivariantClass.capTargetHom_heq_of_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {q : ℤ}
    (F : BivariantClass C G sX sY f hf q) {n n' : ℤ} (h : n = n') {x : chowGroup C sY n}
    {x' : chowGroup C sY n'} (hx : x ≍ x') :
    F.capTargetHom C G sX sY f hf q n x ≍ F.capTargetHom C G sX sY f hf q n' x' := by
  subst h
  cases hx
  rfl

/-- **The restriction of a class caps a class of its own target as the class does at the test
scheme.** For `c ∈ A^p(X ⟶ Y)` and `h : Y' ⟶ Y`, the restriction `res(c) ∈ A^p(X ×_Y Y' ⟶ Y')`
of Stacks 0F9Z caps `β ∈ CH_k(Y')` to `c ∩ β`, the cap of `c` at the test scheme `h`. -/
theorem bivariantRestriction_capTarget {C : ChowSituation.{u}} {G : GysinSystem C}
    (hgys : G.IsNaturalUnderBaseChangeIso) {X Y Y' : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p)
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (k : ℤ) (β : chowGroup C (h ≫ sY) k) :
    (bivariantRestriction C G sX sY f hf h p hgys c).capTarget C G (pullback.fst f h ≫ sX)
        (h ≫ sY) (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) p k
        β =
      c.cap h k β := by
  rw [BivariantClass.capTarget,
    eq_of_heq (bivariantRestriction_cap_id_heq hgys c h k _ β (chowGroupCongr_heq C _ k β)),
    chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
      (by apply pullback.hom_ext <;> simp [pullbackIdIso_inv_eq_fst]) _
      (Category.id_comp _), chowPushforwardOfIso_id]

/-- **Composing with the flat pullback of an open immersion restricts the cap product.** For an
open immersion `j : W ⟶ A` and `b ∈ A^q(A ⟶ B)`, the composite `j^* ∘ b ∈ A^q(W ⟶ B)` of
Stacks 0B75 with the flat pullback class `j^* ∈ A^0(W ⟶ A)` of Stacks 0B78 caps `β ∈ CH_k(B)`
to the restriction of `b ∩ β` to `W`. -/
theorem BivariantClass.capTarget_bivariantCompositeOfInvertible_flatPullback_heq
    (C : ChowSituation.{u}) {W A B : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (j : W ⟶ A) [IsOpenImmersion j] (g : A ⟶ B) [LocallyOfFiniteType g] (hj : j ≫ sA = sW)
    (hg : g ≫ sB = sA) (q : ℤ) (b : BivariantClass C (gysinSystemOfInvertible C) sA sB g hg q)
    (k : ℤ) (β : chowGroup C sB k) :
    (bivariantCompositeOfInvertible C sW sA sB j g hj hg (-((0 : ℕ) : ℤ)) q
        (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sW sA j hj) b).capTarget C
        (gysinSystemOfInvertible C) sW sB (j ≫ g) (comp_comp_structureMorphism_eq hj hg)
        (-((0 : ℕ) : ℤ) + q) k β ≍
      chowGroupRestrict C sA sW j hj (k - q)
        (b.capTarget C (gysinSystemOfInvertible C) sA sB g hg q k β) := by
  set x := b.cap (𝟙 B) k (chowGroupCongr C (Category.id_comp sB).symm k β)
  have hdeg : k - q - -((0 : ℕ) : ℤ) = k - q := by simp
  rw [BivariantClass.capTarget, BivariantClass.capTarget, bivariantCompositeOfInvertible,
    bivariantComposite_cap, bivariantCompositeCap_apply]
  refine HEq.trans (b := chowPushforwardOfIso C (pullback.fst (j ≫ g) (𝟙 B) ≫ sW) sW
    (pullbackIdIso (j ≫ g)).inv (pullbackIdIso_inv_comp _ _) (k - q)
    (chowPushforwardOfIso C (pullback.fst j (pullback.fst g (𝟙 B)) ≫ sW)
      (pullback.fst (j ≫ g) (𝟙 B) ≫ sW) (pullbackRightPullbackFstIso g (𝟙 B) j).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sW j g (𝟙 B)) (k - q)
      (chowGroupRestrict C (pullback.fst g (𝟙 B) ≫ sA)
        (pullback.fst j (pullback.fst g (𝟙 B)) ≫ sW) (pullback.snd j _)
        (pullbackSnd_comp_structureMorphism hj _) (k - q) x))) ?_ (heq_of_eq ?_)
  · refine chowPushforwardOfIso_heq _ _ _ rfl rfl (by ring)
      ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    exact properChowPushforward_heq_congr C _ _ _ _ hdeg _ _ _ _
      (flatPullbackBivariantCap_heq_chowGroupRestrict C sW sA j hj _ (k - q) x)
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_eq_chowGroupRestrict C _ _ _ _
      ((pullbackIdIso (j ≫ g)).hom ≫ (pullbackRightPullbackFstIso g (𝟙 B) j).inv) (by simp),
    chowGroupRestrict_comp,
    chowPushforwardOfIso_eq_chowGroupRestrict C _ _ _ _ (pullbackIdIso g).hom
      (Iso.hom_inv_id _), chowGroupRestrict_comp]
  refine DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ ?_ _) x
  apply pullback.hom_ext <;> simp

end CapTarget

section Restrict

open Stacks.WeilCohomology (canonicalDiagonalClassFamily fieldGysinSystem)

variable {k : Type u} [Field k]

/-- **The canonical intersection product restricts to open subschemes.** For an open immersion
`j : U ⟶ W` of schemes smooth over `k` of the same dimension `N`,
`(a · b)|_U = a|_U · b|_U`. This is flat pullback multiplicativity
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_flatPullbackMul`) in relative dimension
zero, where flat pullback is restriction. -/
theorem chowGroupRestrict_selfIntersectionProduct_canonical {W U : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sU : U ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sU] [Smooth sU]
    (j : U ⟶ W) [IsOpenImmersion j] (hj : j ≫ sW = sU) {N : ℕ} (hN : RelativeDimension sW N)
    (hU : RelativeDimension sU N) (n m : ℤ) (a : chowGroup (fieldChowSituation k) sW n)
    (b : chowGroup (fieldChowSituation k) sW m) :
    chowGroupRestrict (fieldChowSituation k) sW sU j hj (n + m - N)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN) n m a b) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sU N (canonicalDiagonalClassFamily k sU N hU) n m
        (chowGroupRestrict (fieldChowSituation k) sW sU j hj n a)
        (chowGroupRestrict (fieldChowSituation k) sW sU j hj m b) := by
  have hj0 := relativeDimension_of_isOpenImmersion j
  have hfac : ∀ l : ℤ, FlatPullbackFactorsThroughRationalEquivalence (fieldChowSituation k) sU sW
      j hj 0 hj0 l :=
    flatPullbackFactorsThroughRationalEquivalence_general _ sU sW j hj 0 hj0
  refine eq_of_heq ((heq_chowGroupRestrict_flatPullbackChow _ sW sU j hj hj0 _ (hfac _) _).trans
    ((Stacks.WeilCohomology.DiagonalClassFamily.FlatPullbackMul.heq
      (Stacks.WeilCohomology.canonicalDiagonalClassFamily_flatPullbackMul k) sW sU j hj
      (zero_add N).symm hj0 hN hU n m a b).trans ?_))
  exact Stacks.WeilCohomology.selfIntersectionProduct_heq_of_heq sU N _ (by simp) (by simp)
    (heq_chowGroupRestrict_flatPullbackChow _ sW sU j hj hj0 n (hfac n) a).symm
    (heq_chowGroupRestrict_flatPullbackChow _ sW sU j hj hj0 m (hfac m) b).symm

end Restrict

section Parts

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart canonicalDiagonalClassFamily
  fieldGysinSystem)

/-- For open subschemes `U` and `W` of `X`, the restriction `U ∩ W ⟶ W` of the inclusion of `U`
has image `U ∩ W`, read in `W`. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.opensRange_ι_morphismRestrict {X : Scheme.{u}}
    (U W : X.Opens) :
    (U.ι ∣_ W).opensRange = W.ι ⁻¹ᵁ U := by
  ext x
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range, SetLike.mem_coe,
    Scheme.Hom.mem_preimage]
  constructor
  · rintro ⟨y, rfl⟩
    rw [opensι_morphismRestrict_base]
    exact ((U.ι ⁻¹ᵁ W).ι.base y).2
  · intro hx
    obtain ⟨z, hz⟩ : W.ι.base x ∈ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
    obtain ⟨y, hy⟩ : z ∈ Set.range (U.ι ⁻¹ᵁ W).ι.base := by
      rw [Scheme.Opens.range_ι]
      change U.ι.base z ∈ W
      rw [hz]
      exact x.2
    refine ⟨y, opensι_base_injective W ?_⟩
    rw [opensι_morphismRestrict_base, hy, hz]

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]

/-- **The Chow group of codimension `i`** of a scheme `X` smooth over `k`,
`CH^i(X) = ∏_d CH_{d-i}(X_d)`, the product over the open and closed parts `X_d` of `X` of
dimension `d`. A class of `CH_m(X_d)` has codimension `d - m` in `X_d`; the codimension grading is
the one in which the intersection product of Stacks 0FC0 and the Gysin map of a morphism of
smooth schemes are homogeneous. -/
abbrev codimensionChowGroup (i : ℤ) : Type u :=
  ∀ d : ℕ, chowGroup (fieldChowSituation k) (partBase sX d) (d - i)

/-- `CH_n(X) = ∏_d CH_n(X_d)`, the components being restriction to the parts
(`Stacks.Chow.chowGroupClopenRestrictEquiv`). -/
def chowGroupDimPartEquiv (n : ℤ) :
    chowGroup (fieldChowSituation k) sX n ≃+
      ∀ d : ULift.{u} ℕ, chowGroup (fieldChowSituation k) (partBase sX d.down) n :=
  chowGroupClopenRestrictEquiv (fieldChowSituation k) sX
    (fun d : ULift.{u} ℕ ↦ partBase sX d.down)
    (fun d : ULift.{u} ℕ ↦ (dimPart sX d.down).ι) (fun _ ↦ rfl)
    ((isClopenDecomposition_dimPart sX).opensRange_ι_equiv Equiv.ulift) n

/-- The `d`-th component of `chowGroupDimPartEquiv` is the restriction of a class to the part
`X_d`. -/
@[simp]
theorem chowGroupDimPartEquiv_apply (n : ℤ) (α : chowGroup (fieldChowSituation k) sX n)
    (d : ULift.{u} ℕ) :
    chowGroupDimPartEquiv k sX n α d =
      chowGroupRestrict (fieldChowSituation k) sX (partBase sX d.down) (dimPart sX d.down).ι rfl
        n α :=
  chowGroupClopenRestrictEquiv_apply _ _ _ _ _ _ _ _ _

/-- The intersection product of Stacks 0FC0 on the part `X_d` of dimension `d`,
`CH_n(X_d) × CH_m(X_d) ⟶ CH_{n+m-d}(X_d)`, formed with the Gysin class of its diagonal
(Stacks 0FBR). -/
abbrev dimPartIntersectionProduct (d : ℕ) (n m : ℤ) :
    chowGroup (fieldChowSituation k) (partBase sX d) n →ₗ[ℤ]
      chowGroup (fieldChowSituation k) (partBase sX d) m →ₗ[ℤ]
        chowGroup (fieldChowSituation k) (partBase sX d) (n + m - d) :=
  selfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k) (partBase sX d) d
    (canonicalDiagonalClassFamily k (partBase sX d) d (relativeDimension_partBase sX d)) n m

/-- **The intersection product of Stacks 0FC0** on a scheme `X` smooth over `k`,
`CH^i(X) × CH^j(X) ⟶ CH^{i+j}(X)`, formed part by part: `(α · β)_d = α_d · β_d` in
`CH_{(d-i)+(d-j)-d}(X_d) = CH_{d-(i+j)}(X_d)`. -/
def codimensionIntersectionProduct (i j : ℤ) :
    codimensionChowGroup k sX i →ₗ[ℤ] codimensionChowGroup k sX j →ₗ[ℤ]
      codimensionChowGroup k sX (i + j) :=
  LinearMap.mk₂ ℤ
    (fun α β d ↦ chowGroupDegreeEquiv _ _ (by ring : (d : ℤ) - i + (d - j) - d = d - (i + j))
      (dimPartIntersectionProduct k sX d (d - i) (d - j) (α d) (β d)))
    (fun _ _ _ ↦ funext fun _ ↦ by simp)
    (fun _ _ _ ↦ funext fun _ ↦ by simp)
    (fun _ _ _ ↦ funext fun _ ↦ by simp)
    (fun _ _ _ ↦ funext fun _ ↦ by simp)

/-- The `d`-th component of `codimensionIntersectionProduct k sX i j α β` is the intersection
product `α_d · β_d` on `X_d`, regraded from degree `(d - i) + (d - j) - d` to `d - (i + j)`. -/
theorem codimensionIntersectionProduct_apply (i j : ℤ) (α : codimensionChowGroup k sX i)
    (β : codimensionChowGroup k sX j) (d : ℕ) :
    codimensionIntersectionProduct k sX i j α β d =
      chowGroupDegreeEquiv _ _ (by ring : (d : ℤ) - i + (d - j) - d = d - (i + j))
        (dimPartIntersectionProduct k sX d (d - i) (d - j) (α d) (β d)) :=
  rfl

/-- **The intersection product of Stacks 0FC0** of a class `α ∈ CH_n(X)` graded by dimension with
a class `β ∈ CH^j(X)` graded by codimension: the class of `CH_{n-j}(X)` whose restriction to the
part `X_d` is `α|_{X_d} · β_d ∈ CH_{n+(d-j)-d}(X_d)`. -/
def dimensionCodimensionIntersectionProduct (n j : ℤ) :
    chowGroup (fieldChowSituation k) sX n →ₗ[ℤ] codimensionChowGroup k sX j →ₗ[ℤ]
      chowGroup (fieldChowSituation k) sX (n - j) :=
  LinearMap.mk₂ ℤ
    (fun α β ↦ (chowGroupDimPartEquiv k sX (n - j)).symm fun d ↦
      chowGroupDegreeEquiv _ _ (by ring : n + ((d.down : ℤ) - j) - d.down = n - j)
        (dimPartIntersectionProduct k sX d.down n (d.down - j) (chowGroupDimPartEquiv k sX n α d)
          (β d.down)))
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_zsmul]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_zsmul]; congr 1; funext d; simp)

/-- The restriction of `α · β` to the part `X_d` is `α|_{X_d} · β_d`. -/
theorem chowGroupRestrict_dimensionCodimensionIntersectionProduct (n j : ℤ)
    (α : chowGroup (fieldChowSituation k) sX n) (β : codimensionChowGroup k sX j) (d : ℕ) :
    chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl (n - j)
        (dimensionCodimensionIntersectionProduct k sX n j α β) =
      chowGroupDegreeEquiv _ _ (by ring : n + ((d : ℤ) - j) - d = n - j)
        (dimPartIntersectionProduct k sX d n (d - j)
          (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl n α)
          (β d)) := by
  have hdef : dimensionCodimensionIntersectionProduct k sX n j α β =
      (chowGroupDimPartEquiv k sX (n - j)).symm fun d ↦
        chowGroupDegreeEquiv _ _ (by ring : n + ((d.down : ℤ) - j) - d.down = n - j)
          (dimPartIntersectionProduct k sX d.down n (d.down - j)
            (chowGroupDimPartEquiv k sX n α d) (β d.down)) := rfl
  have h := congrFun ((chowGroupDimPartEquiv k sX (n - j)).apply_symm_apply fun d ↦
    chowGroupDegreeEquiv _ _ (by ring : n + ((d.down : ℤ) - j) - d.down = n - j)
      (dimPartIntersectionProduct k sX d.down n (d.down - j)
        (chowGroupDimPartEquiv k sX n α d) (β d.down))) ⟨d⟩
  rw [← hdef, chowGroupDimPartEquiv_apply, chowGroupDimPartEquiv_apply] at h
  exact h

variable {k} (f : X ⟶ Y)

/-- The piece `X_{d,e} = X_d ∩ f⁻¹(Y_e)` of `X`, as an open subscheme of the part `X_d`. -/
abbrev dimPartPiece (d e : ℕ) : (dimPart sX d).toScheme.Opens :=
  (dimPart sX d).ι ⁻¹ᵁ (f ⁻¹ᵁ dimPart sY e)

/-- The structure morphism `X_{d,e} ⟶ Spec k`. -/
abbrev dimPartPieceBase (d e : ℕ) :
    (dimPartPiece sX sY f d e).toScheme ⟶ (fieldChowSituation k).S :=
  (dimPartPiece sX sY f d e).ι ≫ partBase sX d

/-- The inclusion `X_{d,e} ⟶ f⁻¹(Y_e)` of open subschemes of `X`. -/
abbrev dimPartPieceToPreimage (d e : ℕ) :
    (dimPartPiece sX sY f d e).toScheme ⟶ (f ⁻¹ᵁ dimPart sY e).toScheme :=
  (dimPart sX d).ι ∣_ (f ⁻¹ᵁ dimPart sY e)

/-- The restriction `f_{d,e} : X_{d,e} ⟶ Y_e` of `f`. -/
abbrev dimPartPieceHom (d e : ℕ) :
    (dimPartPiece sX sY f d e).toScheme ⟶ (dimPart sY e).toScheme :=
  dimPartPieceToPreimage sX sY f d e ≫ f ∣_ dimPart sY e

/-- The inclusion `X_{d,e} ⟶ f⁻¹(Y_e)` is a morphism over `k`. -/
theorem dimPartPieceToPreimage_comp_base (d e : ℕ) :
    dimPartPieceToPreimage sX sY f d e ≫ ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX) =
      dimPartPieceBase sX sY f d e := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

/-- The inclusion `X_{d,e} ⟶ X ×_Y Y_e` of the piece into the base change of `f` to `Y_e`,
an open immersion. -/
abbrev dimPartPieceToPullback (d e : ℕ) :
    (dimPartPiece sX sY f d e).toScheme ⟶ pullback f (dimPart sY e).ι :=
  dimPartPieceToPreimage sX sY f d e ≫ (pullbackRestrictIsoRestrict f (dimPart sY e)).inv

/-- The inclusion `X_{d,e} ⟶ X ×_Y Y_e`, followed by the projection to `X`, is the inclusion
`X_{d,e} ⟶ X_d ⟶ X`. -/
@[reassoc (attr := simp)]
theorem dimPartPieceToPullback_fst (d e : ℕ) :
    dimPartPieceToPullback sX sY f d e ≫ pullback.fst f (dimPart sY e).ι =
      (dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι := by
  simp [dimPartPieceToPullback, morphismRestrict_ι]

/-- The inclusion `X_{d,e} ⟶ X ×_Y Y_e`, followed by the projection to `Y_e`, is `f_{d,e}`. -/
@[reassoc (attr := simp)]
theorem dimPartPieceToPullback_snd (d e : ℕ) :
    dimPartPieceToPullback sX sY f d e ≫ pullback.snd f (dimPart sY e).ι =
      dimPartPieceHom sX sY f d e := by
  rw [Category.assoc]
  rfl

/-- The inclusion `X_{d,e} ⟶ X ×_Y Y_e` is a morphism over `k`. -/
theorem dimPartPieceToPullback_comp_base (d e : ℕ) :
    dimPartPieceToPullback sX sY f d e ≫ (pullback.fst f (dimPart sY e).ι ≫ sX) =
      dimPartPieceBase sX sY f d e := by
  rw [← Category.assoc, dimPartPieceToPullback_fst, Category.assoc]

variable {f} (hf : f ≫ sY = sX)

include hf in
/-- The restriction `f_{d,e}` of a morphism over `k` is a morphism over `k`. -/
theorem dimPartPieceHom_comp_partBase (d e : ℕ) :
    dimPartPieceHom sX sY f d e ≫ partBase sY e = dimPartPieceBase sX sY f d e := by
  simp [morphismRestrict_ι_assoc, hf]

/-- The piece `X_{d,e}` has dimension `d`. -/
theorem relativeDimension_dimPartPieceBase (d e : ℕ) :
    RelativeDimension (dimPartPieceBase sX sY f d e) d :=
  (zero_add d).subst (motive := RelativeDimension (dimPartPieceBase sX sY f d e))
    (RelativeDimension.comp_of_flat (dimPartPiece sX sY f d e).ι _
      (relativeDimension_opensι _) (relativeDimension_partBase sX d))

/-- The pieces `X_{d,e}`, `e ∈ ℕ`, decompose `X_d` into open and closed subschemes. -/
theorem isClopenDecomposition_dimPartPiece (d : ℕ) :
    IsClopenDecomposition fun e : ULift.{u} ℕ ↦ (dimPartPiece sX sY f d e.down).ι.opensRange :=
  (((isClopenDecomposition_dimPart sY).preimage f).preimage (dimPart sX d).ι).opensRange_ι_equiv
    Equiv.ulift

/-- The pieces `X_{d,e}`, `d ∈ ℕ`, decompose `f⁻¹(Y_e)` into open and closed subschemes. -/
theorem isClopenDecomposition_dimPartPieceToPreimage (e : ℕ) :
    IsClopenDecomposition fun d : ULift.{u} ℕ ↦
      (dimPartPieceToPreimage sX sY f d.down e).opensRange := by
  simp only [dimPartPieceToPreimage, Scheme.Opens.opensRange_ι_morphismRestrict]
  have h := (isClopenDecomposition_dimPart sX).preimage (f ⁻¹ᵁ dimPart sY e).ι
  exact ⟨fun i j hij ↦ h.disjoint _ _ fun h' ↦ hij (ULift.ext h'),
    by rw [← h.iSup_eq_top]; exact Equiv.ulift.iSup_comp (g := fun d ↦ _ ⁻¹ᵁ dimPart sX d)⟩

/-- `CH_n(X_d) = ∏_e CH_n(X_{d,e})`, the components being restriction to the pieces
(`Stacks.Chow.chowGroupClopenRestrictEquiv`). -/
def chowGroupDimPartPieceEquiv (d : ℕ) (n : ℤ) :
    chowGroup (fieldChowSituation k) (partBase sX d) n ≃+
      ∀ e : ULift.{u} ℕ, chowGroup (fieldChowSituation k) (dimPartPieceBase sX sY f d e.down) n :=
  chowGroupClopenRestrictEquiv (fieldChowSituation k) (partBase sX d)
    (fun e : ULift.{u} ℕ ↦ dimPartPieceBase sX sY f d e.down)
    (fun e : ULift.{u} ℕ ↦ (dimPartPiece sX sY f d e.down).ι) (fun _ ↦ rfl)
    (isClopenDecomposition_dimPartPiece sX sY d) n

/-- The `e`-th component of `chowGroupDimPartPieceEquiv` is the restriction of a class of `X_d` to
the piece `X_{d,e}`. -/
@[simp]
theorem chowGroupDimPartPieceEquiv_apply (d : ℕ) (n : ℤ)
    (α : chowGroup (fieldChowSituation k) (partBase sX d) n) (e : ULift.{u} ℕ) :
    chowGroupDimPartPieceEquiv sX sY (f := f) d n α e =
      chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e.down)
        (dimPartPiece sX sY f d e.down).ι rfl n α :=
  chowGroupClopenRestrictEquiv_apply _ _ _ _ _ _ _ _ _

/-- Restricting a class of `X` to `X_{d,e}` through `f⁻¹(Y_e)` is restricting it through `X_d`. -/
theorem chowGroupRestrict_dimPartPieceToPreimage (d e : ℕ) (m : ℤ)
    (γ : chowGroup (fieldChowSituation k) sX m) :
    chowGroupRestrict (fieldChowSituation k) ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPreimage sX sY f d e)
        (dimPartPieceToPreimage_comp_base sX sY f d e) m
        (chowGroupRestrict (fieldChowSituation k) sX ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
          (f ⁻¹ᵁ dimPart sY e).ι rfl m γ) =
      chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e)
        (dimPartPiece sX sY f d e).ι rfl m
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m γ) := by
  rw [chowGroupRestrict_comp, chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr _ _ _ _ _ _ _
    (morphismRestrict_ι (dimPart sX d).ι (f ⁻¹ᵁ dimPart sY e)) _) γ

variable [LocallyOfFiniteType f]

/-- **The Gysin map of `f`, restricted to the piece `X_{d,e}`**, in degree `e - d`: the degree
`e - d` part `f^! ∈ A^{e-d}(X ⟶ Y)` of the Gysin map of Stacks 0FF3
(`Stacks.Chow.smoothGysinClass`), restricted along `Y_e ⟶ Y` (Stacks 0F9Z) to a class in
`A^{e-d}(X ×_Y Y_e ⟶ Y_e)` and then along the open immersion `X_{d,e} ⟶ X ×_Y Y_e`, by composing
(Stacks 0B75) with its flat pullback class (Stacks 0B78), to a class in
`A^{e-d}(X_{d,e} ⟶ Y_e)` for `f_{d,e}`. -/
def dimPartPieceGysinClass (d e : ℕ) :
    BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      (dimPartPieceBase sX sY f d e) (partBase sY e) (dimPartPieceHom sX sY f d e)
      (dimPartPieceHom_comp_partBase sX sY hf d e) ((e : ℤ) - d) :=
  BivariantClass.copy _ _ _ _ (dimPartPieceToPullback_snd sX sY f d e) _ _ (by simp)
    (bivariantCompositeOfInvertible _ (dimPartPieceBase sX sY f d e)
      (pullback.fst f (dimPart sY e).ι ≫ sX) (partBase sY e) (dimPartPieceToPullback sX sY f d e)
      (pullback.snd f (dimPart sY e).ι) (dimPartPieceToPullback_comp_base sX sY f d e)
      (pullbackSnd_comp_structureMorphism_eq _ sX sY f hf _) (-((0 : ℕ) : ℤ)) ((e : ℤ) - d)
      (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible _ _ _ _
        (dimPartPieceToPullback_comp_base sX sY f d e))
      (bivariantRestriction _ _ sX sY f hf (dimPart sY e).ι ((e : ℤ) - d)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)
        (smoothGysinClass _ sX sY hf ((e : ℤ) - d))))

/-- **Stacks 0FF6 for the Gysin map of `f` on a piece.** The restriction of `f^!` to `X_{d,e}`
commutes with every bivariant class: the Gysin map commutes with every class after every base
change (`Stacks.Chow.completedCommutesAfterBaseChange_lciGysinMap`), the flat pullback class of an
open immersion commutes with every class, and so does a composite of such classes. -/
theorem dimPartPieceGysinClass_commutesWithEveryClass (d e : ℕ) :
    (dimPartPieceGysinClass sX sY hf d e).CommutesWithEveryClass := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [dimPartPieceGysinClass, BivariantClass.commutesWithEveryClass_copy]
  exact (commutesWithEveryClass_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible
    _).bivariantCompositeOfInvertible
    (completedCommutesAfterBaseChange_lciGysinMap _ sX sY hf _ _ ((e : ℤ) - d) _)

/-- **Stacks 0FF6 for the Gysin map of `f` on a piece**, in the form the arguments of Stacks 0FFB
and Stacks 0FFC consume: the restriction of `f^!` to `X_{d,e}` commutes with every
`c ∈ A^p(Y_e)`. -/
theorem dimPartPieceGysinClass_bivariantCommute (d e : ℕ) (p : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) (partBase sY e) p) :
    BivariantCommute (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      (partBase sY e) (dimPartPieceHom sX sY f d e) (𝟙 _) ((e : ℤ) - d) p
      (bivariantClassCongrBase _ _ _ (dimPartPieceHom_comp_partBase sX sY hf d e).symm rfl _
        (dimPartPieceGysinClass sX sY hf d e))
      (bivariantClassCongrBase _ _ (𝟙 _) (Category.id_comp _).symm rfl p c) :=
  dimPartPieceGysinClass_commutesWithEveryClass sX sY hf d e (𝟙 _) p _

/-- The restriction of `f^!` to `X_{d,e}` caps `β ∈ CH_m(Y_e)` to the restriction to `X_{d,e}` of
`f^! ∩ β ∈ CH_{m-(e-d)}(X ×_Y Y_e)`, the cap of `f^!` at the test scheme `Y_e ⟶ Y`. -/
theorem dimPartPieceGysinClass_capTarget_heq (d e : ℕ) (m : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) m) :
    (dimPartPieceGysinClass sX sY hf d e).capTarget _ _ _ _ _ _ ((e : ℤ) - d) m β ≍
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPullback sX sY f d e)
        (dimPartPieceToPullback_comp_base sX sY f d e) (m - ((e : ℤ) - d))
        ((smoothGysinClass _ sX sY hf ((e : ℤ) - d)).cap (dimPart sY e).ι m β) := by
  have hcopy : ∀ {g : (dimPartPiece sX sY f d e).toScheme ⟶ (dimPart sY e).toScheme}
      [LocallyOfFiniteType g]
      (hg : dimPartPieceToPullback sX sY f d e ≫ pullback.snd f (dimPart sY e).ι = g)
      (hg' : g ≫ partBase sY e = dimPartPieceBase sX sY f d e) {r : ℤ}
      (hr : -((0 : ℕ) : ℤ) + ((e : ℤ) - d) = r) (a : BivariantClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (dimPartPieceBase sX sY f d e)
        (partBase sY e) _ (comp_comp_structureMorphism_eq
          (dimPartPieceToPullback_comp_base sX sY f d e)
          (pullbackSnd_comp_structureMorphism_eq _ sX sY f hf _)) _),
      (BivariantClass.copy _ _ _ _ hg _ hg' hr a).capTarget _ _ _ _ g hg' r m β ≍
        a.capTarget _ _ _ _ _ _ _ m β := by
    intro g _ hg hg' r hr a
    subst hg hr
    rfl
  refine (hcopy _ _ _ _).trans
    ((BivariantClass.capTarget_bivariantCompositeOfInvertible_flatPullback_heq _ _ _ _ _ _ _ _ _
      _ m β).trans ?_)
  rw [bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)]

/-- **Stacks 0FF7 for `f^!` on a piece.** The degree `e - d` part of the Gysin map of `f`, capped
at the test scheme `Y_e ⟶ Y` with `[Y_e]_e` and restricted to the piece `X_{d,e}` of
`X ×_Y Y_e`, is `[X_{d,e}]_d`, written `[X_{d,e}]_{e-(e-d)}`.

`X` need not have constant dimension, so this is checked on the preimage in `X_{d,e}` of each
connected component `X_w` of `X`. The Gysin map of `f` is homogeneous on `X_w` and satisfies the
cap formula for fundamental classes there
(`Stacks.Chow.SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap`); when `X_w` meets
`X_{d,e}` it lies in `X_d ∩ f⁻¹(Y_e)`, so its generic points have `δ = d` and the connected
component of `Y` containing `f(X_w)` lies in `Y_e`, of pure dimension `e`: the degree on `X_w` is
`e - d`, and `Stacks.Chow.chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula`
applies, every local ring of `Y_e` being Cohen–Macaulay. When `X_w` misses `X_{d,e}` the preimage
is empty. -/
theorem chowGroupRestrict_cap_smoothGysinClass_fundamentalChowClass (d e : ℕ) :
    chowGroupRestrict (fieldChowSituation k) (pullback.fst f (dimPart sY e).ι ≫ sX)
        (dimPartPieceBase sX sY f d e) (dimPartPieceToPullback sX sY f d e)
        (dimPartPieceToPullback_comp_base sX sY f d e) ((e : ℤ) - ((e : ℤ) - d))
        ((smoothGysinClass _ sX sY hf ((e : ℤ) - d)).cap (dimPart sY e).ι e
          (fundamentalChowClass (fieldChowSituation k) (partBase sY e) e)) =
      fundamentalChowClass (fieldChowSituation k) (dimPartPieceBase sX sY f d e)
        ((e : ℤ) - ((e : ℤ) - d)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hlci := isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf
  have hex := GysinMapExists.of_smooth_source f sY sX hf
  set π := (dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι
  have hYe := relativeDimension_partBase sY e
  have hXd := relativeDimension_partBase sX d
  have hT := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (partBase sY e) e hYe
  have hdimV : schemeDeltaDimension (fieldChowSituation k) (dimPartPieceBase sX sY f d e) ≤
      (((e : ℤ) - ((e : ℤ) - d) : ℤ) : EInt) := by
    have h := WeilCohomology.schemeDeltaDimension_le_of_relativeDimension
      (dimPartPieceBase sX sY f d e) (relativeDimension_dimPartPieceBase sX sY d e)
    rwa [show ((e : ℤ) - ((e : ℤ) - d)) = (d : ℤ) by ring]
  have hdimXd : ∀ x : (dimPart sX d).toScheme,
      relativeDimension (fieldChowSituation k).dimensionFunction sX ((dimPart sX d).ι x) ≤ d :=
        fun x ↦ by
    rw [← relativeDimension_comp_isOpenImmersion]
    exact relativeDimension_le_of_schemeDeltaDimension_le' _ _
      (WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _ hXd) x
  -- the Gysin map of `f` is that of its chosen factorization
  obtain ⟨dd, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty f).1 hex) :
    SmoothFactorization f).exists_hasCapFundamentalFormula_gysinMap (fieldChowSituation k) sX sY
      hf hlci
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq
    (C := fieldChowSituation k) _ π _ fun w ↦ ?_
  rw [chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) _ _ _ rfl _ hdimV,
    chowGroupRestrict_comp]
  rcases isEmpty_or_nonempty (π ⁻¹ᵁ X.connectedComponentOpens w).toScheme with hw | ⟨⟨x, hx⟩⟩
  · have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      ((π ⁻¹ᵁ X.connectedComponentOpens w).ι ≫ dimPartPieceBase sX sY f d e)
      ((e : ℤ) - ((e : ℤ) - d))
    exact Subsingleton.elim _ _
  -- the connected component `X_w` lies in `X_d ∩ f⁻¹(Y_e)`
  have hsub : ∀ {Z : Scheme.{u}} (U : Z.Opens), IsClopen (U : Set Z) → ∀ {a b : Z}, a ∈ U →
      ConnectedComponents.mk b = ConnectedComponents.mk a → b ∈ U := fun U hU _ _ hxU hb ↦
    hU.connectedComponent_subset hxU (ConnectedComponents.coe_eq_coe'.1 hb)
  have hXdc : IsClopen ((dimPart sX d : X.Opens) : Set X) :=
    (isClopenDecomposition_dimPart sX).isClopen d
  have hYec : IsClopen ((dimPart sY e : Y.Opens) : Set Y) :=
    (isClopenDecomposition_dimPart sY).isClopen e
  have hxd : π x ∈ dimPart sX d := ((dimPartPiece sX sY f d e).ι x).2
  have hxe : π x ∈ f ⁻¹ᵁ dimPart sY e := x.2
  -- the Gysin map has degree `e - d` on `X_w`
  have hdw : dd w = (e : ℤ) - d := by
    obtain ⟨ξ, hξ, hξw⟩ := exists_mem_genericPoints_mk_eq w
    have hξd : ξ ∈ dimPart sX d := hsub _ hXdc hxd (hξw.trans hx.symm)
    have hξe : f ξ ∈ dimPart sY e :=
      hsub (f ⁻¹ᵁ dimPart sY e) (hYec.preimage f.continuous) hxe (hξw.trans hx.symm)
    have hV : Y.connectedComponentOpens (f.continuous.connectedComponentsMap
        (ConnectedComponents.mk ξ)) ≤ dimPart sY e := by
      exact fun y hy ↦ hsub _ hYec hξe hy
    have hgen : (⟨ξ, hξd⟩ : (dimPart sX d).toScheme) ∈ genericPoints (dimPart sX d).toScheme :=
      (dimPart sX d).ι.isOpenEmbedding.mem_genericPoints_of_image hξ
    have hδ : relativeDimension (fieldChowSituation k).dimensionFunction sX ξ = d := by
      have h := WeilCohomology.relativeDimension_of_mem_irreducibleComponents_of_relativeDimension
        k (partBase sX d) d hXd _ hgen
      exact (relativeDimension_comp_isOpenImmersion _ (dimPart sX d).ι sX
        (⟨ξ, hξd⟩ : (dimPart sX d).toScheme)).symm.trans h
    rw [← hξw, hdeg ξ hξ e fun W ↦ ?_, hδ]
    rw [← WeilCohomology.deltaDimension_congr (Y.homOfLE_ι_assoc hV sY)]
    exact deltaDimension_irreducibleComponents_of_isOpenImmersion (fieldChowSituation k)
      (partBase sY e) hT _ W
  have hres := restriction_completedBivariantSequence (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp (fieldChowSituation k))
    (lciGysinMap (fieldChowSituation k) sX sY hf hlci hex) ((e : ℤ) - d) w
  have hca := (hd w).2 e
  rw [hdw] at hca
  refine chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula
    (fieldChowSituation k) sX sY f hf (completedBivariantSequenceOfInvertible _ sX sY f hf
      (lciGysinMap (fieldChowSituation k) sX sY hf hlci hex) ((e : ℤ) - d)) w
    (hres ▸ hca) (dimPart sY e).ι hT (fun ξ hξ ↦ ?_)
    (fun ξ _ _ ↦ WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k (partBase sY e) _)
    _ _ _ (π.resLE (X.connectedComponentOpens w) (π ⁻¹ᵁ X.connectedComponentOpens w) le_rfl)
    (by rw [Scheme.Hom.resLE_comp_ι, Category.assoc, dimPartPieceToPullback_fst])
  rw [relativeDimension_comp_isOpenImmersion,
    show ((e : ℤ) - ((e : ℤ) - d)) = (d : ℤ) by ring]
  have := hdimXd ⟨_, hsub _ hXdc hxd (hξ.trans hx.symm)⟩
  simpa using this

/-- **Stacks 0FF7 for `f^!` on a piece, at `Y' = Y_e`.** The restriction of the Gysin map of `f`
to `X_{d,e}` carries `[Y_e]_e` to `[X_{d,e}]_d`, written `[X_{d,e}]_{e-(e-d)}`. -/
theorem dimPartPieceGysinClass_capTargetHom_fundamentalChowClass (d e : ℕ) :
    (dimPartPieceGysinClass sX sY hf d e).capTargetHom _ _ _ _ _ _ ((e : ℤ) - d) e
        (fundamentalChowClass (fieldChowSituation k) (partBase sY e) e) =
      fundamentalChowClass (fieldChowSituation k) (dimPartPieceBase sX sY f d e)
        ((e : ℤ) - ((e : ℤ) - d)) := by
  rw [BivariantClass.capTargetHom_apply,
    ← chowGroupRestrict_cap_smoothGysinClass_fundamentalChowClass sX sY hf d e]
  exact eq_of_heq (dimPartPieceGysinClass_capTarget_heq sX sY hf d e _ _)

/-- The Gysin map `f^! : CH_{e-i}(Y_e) ⟶ CH_{d-i}(X_{d,e})` of Stacks 0FF3 on the piece
`X_{d,e}`: cap product with the restriction of the degree `e - d` part of the Gysin map of `f`
to `X_{d,e}` (`Stacks.Chow.dimPartPieceGysinClass`), which lands in
`CH_{(e-i)-(e-d)}(X_{d,e})`. -/
def dimPartPieceGysin (d e : ℕ) (i : ℤ) :
    chowGroup (fieldChowSituation k) (partBase sY e) (e - i) →+
      chowGroup (fieldChowSituation k) (dimPartPieceBase sX sY f d e) (d - i) :=
  (chowGroupDegreeEquiv _ _ (by ring : (e : ℤ) - i - ((e : ℤ) - d) = d - i)).toAddMonoidHom.comp
    ((dimPartPieceGysinClass sX sY hf d e).capTargetHom _ _ _ _ _ _ ((e : ℤ) - d)
      ((e : ℤ) - i))

/-- **The Gysin map of Stacks 0FF3** of a morphism `f : X ⟶ Y` of schemes smooth over `k`,
graded by codimension: `f^! : CH^i(Y) ⟶ CH^i(X)`, `β ↦ f^!β`, where `(f^!β)_d` is the
class of `CH_{d-i}(X_d)` whose restriction to each piece `X_{d,e}` is `f^! β_e`
(`Stacks.Chow.chowGroupRestrict_codimensionGysin`), for `f^!` the Gysin map of `f` restricted to
`X_{d,e}` and `Y_e` (`Stacks.Chow.dimPartPieceGysin`).

The Gysin map of `f` has degree `e - d` on `X_{d,e}`, so this is `f^!` on classes graded by
codimension. See the implementation notes. -/
def codimensionGysin (i : ℤ) : codimensionChowGroup k sY i →+ codimensionChowGroup k sX i :=
  AddMonoidHom.pi fun d ↦
    (chowGroupDimPartPieceEquiv sX sY (f := f) d (d - i)).symm.toAddMonoidHom.comp
      (AddMonoidHom.pi fun e : ULift.{u} ℕ ↦ (dimPartPieceGysin sX sY hf d e.down i).comp
        (Pi.evalAddMonoidHom (fun e : ℕ ↦ chowGroup (fieldChowSituation k) (partBase sY e)
          (e - i)) e.down))

/-- **The restriction of `f^!β` to the piece `X_{d,e}` is `f^! β_e`**, for `f^!` the Gysin map of
`f` restricted to `X_{d,e}` and `Y_e`. -/
theorem chowGroupRestrict_codimensionGysin (i : ℤ) (β : codimensionChowGroup k sY i) (d e : ℕ) :
    chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e)
        (dimPartPiece sX sY f d e).ι rfl (d - i) (codimensionGysin sX sY hf i β d) =
      dimPartPieceGysin sX sY hf d e i (β e) := by
  have h := congrFun ((chowGroupDimPartPieceEquiv sX sY (f := f) d (d - i)).apply_symm_apply
    fun e : ULift.{u} ℕ ↦ dimPartPieceGysin sX sY hf d e.down i (β e.down)) ⟨e⟩
  rw [chowGroupDimPartPieceEquiv_apply] at h
  exact h

end Parts

/-- The Gysin map in a single degree respects heterogeneous equality of its argument, whose degree
may be written differently. -/
theorem smoothGysinChow_heq_of_heq {C : ChowSituation.{u}} {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [Smooth sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [Smooth sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (q : ℤ) {n n' : ℤ} (h : n = n')
    {x : chowGroup C sY n} {x' : chowGroup C sY n'} (hx : x ≍ x') :
    smoothGysinChow C sX sY hf q n x ≍ smoothGysinChow C sX sY hf q n' x' :=
  BivariantClass.capTargetHom_heq_of_heq _ h hx

/-- **Stacks 0FF7 for a morphism of schemes smooth over a field, at `Y' = Y`.** Let `g : W ⟶ V`
be a morphism of schemes smooth over a field `k`, with `W` of constant dimension `d` and `V` of
constant dimension `e`. Then the Gysin map `g^!` of Stacks 0FF3, in its degree `e - d`, carries
`[V]_e` to `[W]_d`, written `[W]_{e-(e-d)}` in the degree that `g^!` produces.

Every irreducible component of `W` and of `V` has `δ`-dimension `d` and `e`
(`Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension`), every local
ring of `V` is Cohen–Macaulay (`Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth`),
and Stacks 0FF7 in a single degree at the test scheme `𝟙 V`
(`Stacks.Chow.cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass`) gives
`g^! ∩ [V]_e = [W ×_V V]_d`, which is `[W]_d` under `W ×_V V ≅ W`. -/
theorem smoothGysinChow_fundamentalChowClass {k : Type u} [Field k] {W V : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [Smooth sW] (sV : V ⟶ (fieldChowSituation k).S)
    [Smooth sV] {g : W ⟶ V} [LocallyOfFiniteType g] (hg : g ≫ sV = sW) (d e : ℕ)
    (hd : RelativeDimension sW d) (he : RelativeDimension sV e) :
    smoothGysinChow (fieldChowSituation k) sW sV hg ((e : ℤ) - d) e
        (fundamentalChowClass (fieldChowSituation k) sV e) =
      fundamentalChowClass (fieldChowSituation k) sW ((e : ℤ) - ((e : ℤ) - d)) := by
  -- `W ×_V V ≅ W` has every point of `δ` at most `d`
  have hdim : ∀ ξ : (pullback g (𝟙 V) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst g (𝟙 V) ≫ sW) ξ ≤
        (e : ℤ) - ((e : ℤ) - d) := fun ξ ↦ by
    rw [relativeDimension_comp_isOpenImmersion]
    exact (relativeDimension_le_of_schemeDeltaDimension_le' _ sW
      (WeilCohomology.schemeDeltaDimension_le_of_relativeDimension sW hd) _).trans_eq (by ring)
  -- every local ring of `V` is Cohen–Macaulay
  have hCM : ∀ ξ : (pullback g (𝟙 V) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst g (𝟙 V) ≫ sW) ξ =
        (e : ℤ) - ((e : ℤ) - d) →
      let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (𝟙 V ≫ sV)
      IsCohenMacaulayLocalRing (V.presheaf.stalk (pullback.snd g (𝟙 V) ξ)) :=
    fun ξ _ ↦ WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k sV _
  have key := cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass
    (fieldChowSituation k) sW sV hg
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth g sV sW hg)
    (GysinMapExists.of_smooth_source g sV sW hg) (𝟙 V) (n := d) (m := e) (m' := e)
    (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sW d hd)
    (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sV e he)
    (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k (𝟙 V ≫ sV) e
      (by simpa only [Category.id_comp] using he)) hdim hCM
  rw [smoothGysinChow, lciGysinChow, BivariantClass.capTargetHom_apply, BivariantClass.capTarget,
    chowGroupCongr_fundamentalChowClass, key]
  exact chowPushforwardOfIso_fundamentalChowClass _ _ _ _ _ _

section Theorems

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  canonicalDiagonalClassFamily fieldGysinSystem
  capFundamentalClassSurjective canonicalDiagonalClassFamily_capEqProduct
  selfIntersectionProduct_heq_of_heq)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
  {f : X ⟶ Y} [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- **Stacks 0FFB: `f^!(α · β) = f^!α · f^!β`.** Let `f : X ⟶ Y` be a morphism of schemes
smooth over a field `k`, of arbitrary and not necessarily constant dimension. Then
`f` is a local complete intersection morphism for which the Gysin map `f^!` of Stacks 0FF3 exists
(`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_smooth_of_smooth`,
`Stacks.Chow.GysinMapExists.of_smooth_source`), and for `α ∈ CH^i(Y)` and `β ∈ CH^j(Y)`

  `f^!(α · β) = f^!α · f^!β`   in   `CH^{i+j}(X)`,

for `f^!` the Gysin map of `f` acting on classes graded by codimension
(`Stacks.Chow.codimensionGysin`) and the intersection product
`Stacks.Chow.codimensionIntersectionProduct` of Stacks 0FC0, formed part by part on the open
and closed parts of `X` and `Y` of constant dimension.

Both sides are compared on each piece `X_{d,e}`, where `f^!` is the Gysin map of `f` restricted to
`X_{d,e}` and `Y_e` (`Stacks.Chow.dimPartPieceGysinClass`): the left is `f^!(α_e · β_e)`; the
right is the restriction of a product on `X_d`, which is the product of the restrictions
(`Stacks.Chow.chowGroupRestrict_selfIntersectionProduct_canonical`); and the two agree by the
source's argument (`Stacks.Chow.BivariantClass.capTargetHom_selfIntersectionProduct`), whose
inputs Stacks 0FF7 and Stacks 0FF6 for `f^!` on the piece are
`Stacks.Chow.dimPartPieceGysinClass_capTargetHom_fundamentalChowClass` and
`Stacks.Chow.dimPartPieceGysinClass_bivariantCommute`. -/
@[stacks 0FFB "the whole statement for a morphism `f` of schemes smooth over a field, of \
arbitrary dimension: its Gysin map `f^!` exists and `f^!(α · β) = f^!α · f^!β`, for `f^!` the \
Gysin map of `f` itself acting part by part and products formed part by part on the open and \
closed parts of constant dimension"]
theorem codimensionGysin_codimensionIntersectionProduct
    (i j : ℤ) (α : codimensionChowGroup k sY i) (β : codimensionChowGroup k sY j) :
    codimensionGysin sX sY hf (i + j) (codimensionIntersectionProduct k sY i j α β) =
      codimensionIntersectionProduct k sX i j (codimensionGysin sX sY hf i α)
        (codimensionGysin sX sY hf j β) := by
  funext d
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d (d - (i + j))).injective
    (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  have hV := relativeDimension_dimPartPieceBase sX sY (f := f) d e
  have hYe := relativeDimension_partBase sY e
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin, codimensionIntersectionProduct_apply,
    codimensionIntersectionProduct_apply, chowGroupRestrict_chowGroupDegreeEquiv,
    chowGroupRestrict_selfIntersectionProduct_canonical _ _ _ _
      (relativeDimension_partBase sX d) hV,
    chowGroupRestrict_codimensionGysin, chowGroupRestrict_codimensionGysin]
  have key := BivariantClass.capTargetHom_selfIntersectionProduct (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_of_isClosed k) (dimPartPieceBase sX sY f d e) (partBase sY
        e)
    (dimPartPieceHom_comp_partBase sX sY hf d e) d e
    (canonicalDiagonalClassFamily k _ d hV) (canonicalDiagonalClassFamily k _ e hYe)
    (dimPartPieceGysinClass sX sY hf d e)
    (dimPartPieceGysinClass_capTargetHom_fundamentalChowClass sX sY hf d e)
    (dimPartPieceGysinClass_bivariantCommute sX sY hf d e)
    (fun p ↦ capFundamentalClassSurjective k _ e hYe p)
    (canonicalDiagonalClassFamily_capEqProduct k _ e hYe)
    (canonicalDiagonalClassFamily_capEqProduct k _ d hV) (e - i) (e - j) (α e) (β e)
  simp only [dimPartPieceGysin, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    ((BivariantClass.capTargetHom_heq_of_heq _ (by ring)
      (chowGroupDegreeEquiv_heq _ _ _ _)).trans ?_))
  rw [key]
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans
    (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  exact selfIntersectionProduct_heq_of_heq _ _ _ (by ring) (by ring)
    (chowGroupDegreeEquiv_heq _ _ _ _).symm (chowGroupDegreeEquiv_heq _ _ _ _).symm

end Theorems

section ProjectionFormula

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  canonicalDiagonalClassFamily fieldGysinSystem
  capFundamentalClassSurjective canonicalDiagonalClassFamily_capEqProduct
  selfIntersectionProduct_heq_of_heq)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
  {f : X ⟶ Y} [IsProper f] (hf : f ≫ sY = sX)

/-- **Stacks 0FFC: the projection formula `f_*(α · f^!β) = f_*α · β`.** Let `f : X ⟶ Y` be a
proper morphism of schemes smooth over a field `k`, of arbitrary and not
necessarily constant dimension. Then the Gysin map `f^!` of Stacks 0FF3 exists
(`Stacks.Chow.GysinMapExists.of_smooth_source`), and for `α ∈ CH_n(X)` and `β ∈ CH^j(Y)`

  `f_*(α · f^!β) = f_*α · β`   in   `CH_{n-j}(Y)`,

for `f^!` the Gysin map of `f` acting on classes graded by codimension
(`Stacks.Chow.codimensionGysin`) and the intersection product
`Stacks.Chow.dimensionCodimensionIntersectionProduct` of Stacks 0FC0, formed part by part on the
open and closed parts of `X` and `Y` of constant dimension.

Both sides are compared on each part `Y_e` of `Y`, where `f_*` becomes the pushforward from
`f⁻¹(Y_e)`. Writing `β_e = c ∩ [Y_e]_e` (Stacks 0FC2), one has `γ · β_e = c ∩ γ` and
`c ∩ f_*α = f_*(res(c) ∩ α)` (`Stacks.Chow.chowCohomologyCap_properChowPushforward_restriction`),
and `α · f^!β = res(c) ∩ α` on `f⁻¹(Y_e)`, checked on each piece `X_{d,e}`: there
`f^!β_e = res(c) ∩ [X_{d,e}]_d` by Stacks 0FF6 and Stacks 0FF7 for the Gysin map of `f`
restricted to the piece
(`Stacks.Chow.BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq`,
`Stacks.Chow.dimPartPieceGysinClass_bivariantCommute`,
`Stacks.Chow.dimPartPieceGysinClass_capTargetHom_fundamentalChowClass`), and
`α · (res(c) ∩ [X_{d,e}]_d) = res(c) ∩ α` by Stacks 0FC2 and the symmetry of the product. -/
@[stacks 0FFC "the whole statement for a proper morphism `f` of schemes smooth over a field, \
of arbitrary dimension: its Gysin map `f^!` exists and `f_*(α · f^!β) = f_*α · β`, for `f^!` \
the Gysin map of `f` itself acting part by part and products formed part by part on the open \
and closed parts of constant dimension"]
theorem properChowPushforward_dimensionCodimensionIntersectionProduct_codimensionGysin
    (n j : ℤ) (α : chowGroup (fieldChowSituation k) sX n) (β : codimensionChowGroup k sY j) :
    properChowPushforward (fieldChowSituation k) sX sY f hf (n - j)
        (properPushforwardDescends _ _ _ _ _ _)
        (dimensionCodimensionIntersectionProduct k sX n j α (codimensionGysin sX sY hf j β)) =
      dimensionCodimensionIntersectionProduct k sY n j
        (properChowPushforward (fieldChowSituation k) sX sY f hf n
          (properPushforwardDescends _ _ _ _ _ _) α) β := by
  refine (chowGroupDimPartEquiv k sY (n - j)).injective (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  have hYe := relativeDimension_partBase sY e
  have hfe : f ∣_ dimPart sY e ≫ partBase sY e = (f ⁻¹ᵁ dimPart sY e).ι ≫ sX :=
    morphismRestrict_comp_opensι_comp f (dimPart sY e) sX sY hf
  have hpush : ∀ (m : ℤ) (γ : chowGroup (fieldChowSituation k) sX m),
      chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl m
          (properChowPushforward (fieldChowSituation k) sX sY f hf m
            (properPushforwardDescends _ _ _ _ _ _) γ) =
        properChowPushforward (fieldChowSituation k) ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
          (partBase sY e) (f ∣_ dimPart sY e) hfe m (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupRestrict (fieldChowSituation k) sX ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
            (f ⁻¹ᵁ dimPart sY e).ι rfl m γ) := by
    intro m γ
    rw [chowGroupRestrict_opensι, chowGroupRestrict_opensι]
    exact chowGroupOpensRestrict_properChowPushforward _ sX sY f hf (dimPart sY e) m _ _ _ _ γ
  rw [chowGroupDimPartEquiv_apply, chowGroupDimPartEquiv_apply,
    chowGroupRestrict_dimensionCodimensionIntersectionProduct, hpush, hpush]
  obtain ⟨c, hc⟩ := capFundamentalClassSurjective k (partBase sY e) e hYe j (β e)
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  -- the source's computation on `f⁻¹(Y_e)`: `α · f^!β = res(c) ∩ α`
  have hMC : chowGroupRestrict (fieldChowSituation k) sX ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
        (f ⁻¹ᵁ dimPart sY e).ι rfl (n - j)
        (dimensionCodimensionIntersectionProduct k sX n j α (codimensionGysin sX sY hf j β)) =
      chowCohomologyCap (fieldChowSituation k) (fieldGysinSystem k) ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX) j
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) _ (partBase sY e) hfe
          (fieldGysinSystem k) hgys j c)
        n (chowGroupRestrict (fieldChowSituation k) sX ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
          (f ⁻¹ᵁ dimPart sY e).ι rfl n α) := by
    refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX)
      (fun d : ULift.{u} ℕ ↦ dimPartPieceBase sX sY f d.down e)
      (fun d : ULift.{u} ℕ ↦ dimPartPieceToPreimage sX sY f d.down e)
      (fun d ↦ dimPartPieceToPreimage_comp_base sX sY f d.down e)
      (isClopenDecomposition_dimPartPieceToPreimage sX sY e) (n - j)).injective
      (funext fun d ↦ ?_)
    obtain ⟨d⟩ := d
    have hV := relativeDimension_dimPartPieceBase sX sY (f := f) d e
    have hde := dimPartPieceHom_comp_partBase sX sY hf d e
    rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply,
      chowGroupRestrict_chowCohomologyCap_restrictionOfEq, chowGroupRestrict_dimPartPieceToPreimage,
      chowGroupRestrict_dimPartPieceToPreimage,
      chowGroupRestrict_dimensionCodimensionIntersectionProduct,
      chowGroupRestrict_chowGroupDegreeEquiv,
      chowGroupRestrict_selfIntersectionProduct_canonical _ _ _ _
        (relativeDimension_partBase sX d) hV, chowGroupRestrict_codimensionGysin, ← hc]
    set x := chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sX sY f d e)
      (dimPartPiece sX sY f d e).ι rfl n
      (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl n α)
    set r := chowCohomologyRestrictionOfEq (fieldChowSituation k) (dimPartPieceBase sX sY f d e)
      (partBase sY e) hde (fieldGysinSystem k) hgys j c
    -- `f^!β = res(c) ∩ [X_{d,e}]_d`, by Stacks 0FF6 and Stacks 0FF7
    have hβ : dimPartPieceGysin sX sY hf d e j
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
          (partBase sY e) e j c) ≍
        chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
          (dimPartPieceBase sX sY f d e) d j r := by
      exact (chowGroupDegreeEquiv_heq _ _ _ _).trans
        (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq _ _ hgys _ _ j hde
          ((e : ℤ) - d) (dimPartPieceGysinClass sX sY hf d e) c
          (dimPartPieceGysinClass_bivariantCommute sX sY hf d e j c) e
          (dimPartPieceGysinClass_capTargetHom_fundamentalChowClass sX sY hf d e) (by ring))
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    refine (selfIntersectionProduct_heq_of_heq _ _ _ rfl (by ring) HEq.rfl hβ).trans ?_
    rw [Stacks.WeilCohomology.canonicalDiagonalClassFamily_isSymmetric k,
      canonicalDiagonalClassFamily_capEqProduct k _ d hV j r n x]
    exact (chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _).symm
  rw [hMC, ← chowCohomologyCap_properChowPushforward_restriction (fieldChowSituation k)
    (fieldGysinSystem k) hgys
    ((f ⁻¹ᵁ dimPart sY e).ι ≫ sX) (partBase sY e) hfe j c n, ← hc,
    canonicalDiagonalClassFamily_capEqProduct k _ e hYe j c n,
    Stacks.WeilCohomology.canonicalDiagonalClassFamily_isSymmetric k _ e hYe]
  exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _).symm))

end ProjectionFormula

end Stacks.Chow

end
