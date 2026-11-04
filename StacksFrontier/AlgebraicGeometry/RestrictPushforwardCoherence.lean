module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlue

/-!
# Coherence of the restriction and pushforward peeling isomorphisms

A glueing datum `AlgebraicGeometry.AffineOpensGlue.ChartComparison` on the affine opens of a
scheme `X` asks for a comparison between the restrictions to the smaller chart of the
*pushforwards to `X`* of its two members, and for the cocycle condition on those comparisons.
The mathematical input is always of a different shape: an isomorphism
`mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE h)` between a member and the restriction of
the larger member along the inclusion `V ⟶ W`, together with the cocycle condition for *those*.

This file peels the pushforwards off and proves that the two cocycle conditions agree. The two
peeling isomorphisms are the counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`,
which is an isomorphism, and the comparison of the restriction along `V ⟶ X` with the
composition of the restrictions along `V ⟶ W ⟶ X`. Their coherence is the pentagon for
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, which is proved here: Mathlib ships the
pseudofunctor coherences for `AlgebraicGeometry.Scheme.Modules.pullback` only, and transporting
them along `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is longer than proving
the pentagon directly, every component in sight being a restriction map of a presheaf.

## Main definitions

* `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso`: **the first peeling isomorphism**,
  `Scheme.Modules.restrict ((Scheme.Modules.pushforward U.ι).obj N) U.ι ≅ N`.
* `AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso`: the comparison of the restriction along
  `V ⟶ X` with the composition of the restrictions along `V ⟶ W` and `W ⟶ X`, as an isomorphism
  of functors.
* `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso`: **the second peeling
  isomorphism**, `Scheme.Modules.restrict ((Scheme.Modules.pushforward W.ι).obj M) V.ι ≅
  Scheme.Modules.restrict M (X.homOfLE h)` for opens `V ≤ W`.
* `AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso`: the comparison of the composition
  of the restrictions along `V ⟶ V'` and `V' ⟶ W` with the restriction along `V ⟶ W`.
* `AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso` and
  `AlgebraicGeometry.AffineOpensGlue.ofRestrictIso`: **the glueing datum built from a family of
  isomorphisms `mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE h)`**.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso_hom_naturality` and
  `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso_hom_naturality`: the two peeling
  isomorphisms are natural in the module.
* `AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso_hom_app_trans`: **the pentagon for
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`** along a chain `V ≤ V' ≤ W` of opens.
* `AlgebraicGeometry.AffineOpensGlue.restrictLocal_eq`: **`AlgebraicGeometry.restrictLocal` is
  the conjugate of the restricted morphism** by `restrictCompNatIso`.
* `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso_hom_trans`: **the second peeling
  isomorphism is transitive**, which is the pentagon read at a pushforward.
* `AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso`: **the reduction lemma.** The
  comparisons obtained by peeling satisfy the cocycle condition of
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison` as soon as the family of isomorphisms they
  were peeled from satisfies its own cocycle condition.

## Implementation notes

`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso` and
`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso` repeat, verbatim,
`AlgebraicGeometry.DeterminantTwoTerm.restrictPushforwardIso` and
`AlgebraicGeometry.DeterminantTwoTerm.restrictPushforwardLeIso`; the definitions agree on the
nose, so the reduction lemma applies to the determinant's comparison as well, but this file is
kept free of the determinant so that the glueing plumbing does not depend on it.

Every structural isomorphism used here — `restrictFunctorCongr`, `restrictFunctorComp` and the
counit of `restrictAdjunction` — has, at every open, a *restriction map of a presheaf* as its
component, and any two restriction maps with the same source and target agree because the homs
of a poset are unique. So the pentagon
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso_hom_app_trans` is proved by checking the
components, collapsing each side to a single `Functor.map` with `← Functor.map_comp` and
appealing to `AlgebraicGeometry.presheaf_map_eq`. Everything else is formal manipulation of
isomorphisms in a category, with no further unfolding.

The three-fold inequalities are carried as separate arguments (`h : V ≤ V'`, `h' : V' ≤ W` and
`hVW : V ≤ W`) rather than as `h.trans h'`, which is only definitionally the third. Proofs of
`≤` are propositions and so are interchangeable, but `rw` matches syntactically, and spelling
the third inequality separately lets the lemmas be applied at whatever proof the caller holds.

## References

* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AffineOpensGlue

variable {X : Scheme.{u}}

/-! ### The peeling isomorphisms -/

/-- **The restriction to an open subscheme of a pushforward from it is the original module.**
This is the counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, which is an
isomorphism. -/
def restrictPushforwardIso {Y : Scheme.{u}} {U : Y.Opens} (N : (U : Scheme.{u}).Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward U.ι).obj N) U.ι ≅ N :=
  (asIso (Scheme.Modules.restrictAdjunction U.ι).counit).app N

/-- The forward map of `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso` is the
component of the counit. -/
@[simp]
theorem restrictPushforwardIso_hom {Y : Scheme.{u}} {U : Y.Opens}
    (N : (U : Scheme.{u}).Modules) :
    (restrictPushforwardIso N).hom = (Scheme.Modules.restrictAdjunction U.ι).counit.app N :=
  rfl

/-- **The first peeling isomorphism is natural in the module**, being a component of the counit
of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
theorem restrictPushforwardIso_hom_naturality {Y : Scheme.{u}} {U : Y.Opens}
    {N N' : (U : Scheme.{u}).Modules} (α : N ⟶ N') :
    (restrictPushforwardIso N).hom ≫ α =
      (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward U.ι).map α) ≫
        (restrictPushforwardIso N').hom :=
  ((Scheme.Modules.restrictAdjunction U.ι).counit.naturality α).symm

/-- **The restriction along an inclusion of opens, split in two.** For opens `V ≤ W` of `X`, the
restriction functor along `V ⟶ X` is the restriction along `W ⟶ X` followed by the restriction
along the inclusion `V ⟶ W`, because `V ⟶ W ⟶ X` is `V ⟶ X`. -/
def restrictCompNatIso {V W : X.Opens} (h : V ≤ W) :
    Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι

/-- **The restriction to a smaller open of a pushforward from a larger one.** For opens `V ≤ W`
of `X` and a module `M` on `W`, the restriction to `V` of the pushforward of `M` to `X` is the
restriction of `M` along the inclusion `V ⟶ W`.

The restriction along `V ⟶ X` is split in two by
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso`, and the inner one is
`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso`. -/
def restrictPushforwardLeIso {V W : X.Opens} (h : V ≤ W) (M : (W : Scheme.{u}).Modules) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward W.ι).obj M) V.ι ≅
      Scheme.Modules.restrict M (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso (restrictPushforwardIso M)

/-- The forward map of the second peeling isomorphism, read through
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso`. -/
theorem restrictPushforwardLeIso_hom {V W : X.Opens} (h : V ≤ W)
    (M : (W : Scheme.{u}).Modules) :
    (restrictPushforwardLeIso h M).hom =
      (restrictCompNatIso h).hom.app ((Scheme.Modules.pushforward W.ι).obj M) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (restrictPushforwardIso M).hom := by
  dsimp only [restrictPushforwardLeIso, restrictCompNatIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Category.assoc]

/-- **The second peeling isomorphism is natural in the module**, by the naturality of
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso` and of the first one. -/
theorem restrictPushforwardLeIso_hom_naturality {V W : X.Opens} (h : V ≤ W)
    {M M' : (W : Scheme.{u}).Modules} (α : M ⟶ M') :
    (restrictPushforwardLeIso h M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map α =
      (Scheme.Modules.restrictFunctor V.ι).map ((Scheme.Modules.pushforward W.ι).map α) ≫
        (restrictPushforwardLeIso h M').hom := by
  have hΞ := (restrictCompNatIso h).hom.naturality ((Scheme.Modules.pushforward W.ι).map α)
  dsimp only [Functor.comp_map] at hΞ
  rw [restrictPushforwardLeIso_hom, restrictPushforwardLeIso_hom, Category.assoc,
    ← Functor.map_comp, restrictPushforwardIso_hom_naturality α, Functor.map_comp,
    ← Category.assoc, ← hΞ, Category.assoc]

/-! ### The pentagon -/

/-- **The restrictions along a chain of two inclusions of opens compose.** For opens
`V ≤ V' ≤ W` of `X`, the restriction along `V' ⟶ W` followed by the restriction along `V ⟶ V'`
is the restriction along `V ⟶ W`. -/
def restrictFunctorTransIso {V V' W : X.Opens} (h : V ≤ V') (h' : V' ≤ W) (hVW : V ≤ W) :
    Scheme.Modules.restrictFunctor (X.homOfLE h') ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE h) ≅
      Scheme.Modules.restrictFunctor (X.homOfLE hVW) :=
  (Scheme.Modules.restrictFunctorComp (X.homOfLE h) (X.homOfLE h')).symm ≪≫
    Scheme.Modules.restrictFunctorCongr
      (show X.homOfLE h ≫ X.homOfLE h' = X.homOfLE hVW from X.homOfLE_homOfLE h h')

/-- **The pentagon for `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`.** For opens
`V ≤ V' ≤ W` of `X`, splitting the restriction along `V ⟶ X` as `V ⟶ W ⟶ X` is the same as
splitting it as `V ⟶ V' ⟶ X` and then splitting the restriction along `V' ⟶ X` as
`V' ⟶ W ⟶ X`.

Every component in sight is a restriction map of the presheaf of `N`, and any two restriction
maps with the same source and target agree, the homs of a poset being unique. -/
theorem restrictCompNatIso_hom_app_trans {V V' W : X.Opens} (h : V ≤ V') (h' : V' ≤ W)
    (hVW : V ≤ W) (N : X.Modules) :
    (restrictCompNatIso hVW).hom.app N =
      (restrictCompNatIso h).hom.app N ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
          ((restrictCompNatIso h').hom.app N) ≫
        (restrictFunctorTransIso h h' hVW).hom.app (Scheme.Modules.restrict N W.ι) := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  dsimp only [restrictCompNatIso, restrictFunctorTransIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    restrictFunctor_map_app, Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, Scheme.Modules.restrict_map,
    Category.assoc]
  dsimp only [Scheme.Modules.restrict_obj, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp]
  exact presheaf_map_eq N _ _

/-- **The second peeling isomorphism is transitive.** For opens `V ≤ V' ≤ W` of `X` and a module
`M` on `W`, peeling the pushforward of `M` off over `V` is peeling it off over `V'` and then
restricting to `V`. This is the pentagon
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso_hom_app_trans` read at the pushforward of
`M`, together with the naturality of
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso`. -/
theorem restrictPushforwardLeIso_hom_trans {V V' W : X.Opens} (h : V ≤ V') (h' : V' ≤ W)
    (hVW : V ≤ W) (M : (W : Scheme.{u}).Modules) :
    (restrictPushforwardLeIso hVW M).hom =
      (restrictCompNatIso h).hom.app ((Scheme.Modules.pushforward W.ι).obj M) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
          (restrictPushforwardLeIso h' M).hom ≫
        (restrictFunctorTransIso h h' hVW).hom.app M := by
  have hnat := (restrictFunctorTransIso h h' hVW).hom.naturality (restrictPushforwardIso M).hom
  dsimp only [Functor.comp_map] at hnat
  rw [restrictPushforwardLeIso_hom hVW M,
    restrictCompNatIso_hom_app_trans h h' hVW ((Scheme.Modules.pushforward W.ι).obj M),
    restrictPushforwardLeIso_hom h' M, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hnat]

/-! ### `restrictLocal` as a conjugation -/

/-- **`AlgebraicGeometry.restrictLocal` is a conjugate.** The restriction to a smaller open `V`
of a morphism of the restrictions to `W` is the restriction of that morphism along `V ⟶ W`,
conjugated by `AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso`. This holds by
associativity: `AlgebraicGeometry.restrictLocal` is literally the four-fold composite that
`restrictCompNatIso` repackages as two. -/
theorem restrictLocal_eq {A B : X.Modules} {V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W) :
    restrictLocal φ hV =
      (restrictCompNatIso hV).hom.app A ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hV)).map φ ≫
        (restrictCompNatIso hV).inv.app B := by
  dsimp only [restrictLocal, restrictCompNatIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]

/-! ### The two consequences the reduction needs -/

/-- The backward map of the second peeling isomorphism, read through
`AlgebraicGeometry.AffineOpensGlue.restrictCompNatIso`. -/
theorem restrictPushforwardLeIso_inv {V W : X.Opens} (h : V ≤ W)
    (M : (W : Scheme.{u}).Modules) :
    (restrictPushforwardLeIso h M).inv =
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (restrictPushforwardIso M).inv ≫
        (restrictCompNatIso h).inv.app ((Scheme.Modules.pushforward W.ι).obj M) := by
  dsimp only [restrictPushforwardLeIso, restrictCompNatIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, NatTrans.comp_app, Functor.mapIso_inv,
    Category.assoc]

/-- Peeling a pushforward off over `V` and splitting the restriction along `V ⟶ X` undo each
other, leaving the restriction along `V ⟶ W` of the inverse of the first peeling
isomorphism. -/
@[reassoc]
theorem restrictPushforwardLeIso_inv_comp {V W : X.Opens} (h : V ≤ W)
    (M : (W : Scheme.{u}).Modules) :
    (restrictPushforwardLeIso h M).inv ≫
        (restrictCompNatIso h).hom.app ((Scheme.Modules.pushforward W.ι).obj M) =
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (restrictPushforwardIso M).inv := by
  rw [restrictPushforwardLeIso_inv, Category.assoc]
  simp

/-- `AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso_hom_trans`, read on the inverses:
the composition of the restrictions absorbs the peeling over `V'` followed by the splitting of
the restriction along `V ⟶ X`. -/
@[reassoc]
theorem restrictFunctorTransIso_hom_app_comp_inv {V V' W : X.Opens} (h : V ≤ V') (h' : V' ≤ W)
    (hVW : V ≤ W) (M : (W : Scheme.{u}).Modules) :
    (restrictFunctorTransIso h h' hVW).hom.app M ≫ (restrictPushforwardLeIso hVW M).inv =
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
          (restrictPushforwardLeIso h' M).inv ≫
        (restrictCompNatIso h).inv.app ((Scheme.Modules.pushforward W.ι).obj M) := by
  rw [Iso.comp_inv_eq, restrictPushforwardLeIso_hom_trans h h' hVW M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-! ### The reduction of the cocycle condition -/

/-- An inclusion of affine opens of `X`, read as an inclusion of the underlying opens. The two
are definitionally the same; the named form pins the spelling the declarations below use. -/
theorem coe_le_coe {V W : X.affineOpens} (h : V ≤ W) : (V.1 : X.Opens) ≤ (W.1 : X.Opens) := h

variable (mod : ∀ V : X.affineOpens, ((V.1 : X.Opens) : Scheme.{u}).Modules)

/-- **The comparison of a glueing datum, built by peeling the pushforwards off.** Given a module
on each affine open and, for each inclusion `V ≤ W`, an isomorphism of the module on `V` with the
restriction along `V ⟶ W` of the module on `W`, this is the comparison of the restrictions to `V`
of the pushforwards to `X` that
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.comp` asks for: the two peeling isomorphisms
with the given one in the middle. -/
def compOfRestrictIso
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE (coe_le_coe h)))
    (V W : X.affineOpens) (h : V ≤ W) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X V)).obj (mod V))
        (V.1 : X.Opens).ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X W)).obj (mod W))
        (V.1 : X.Opens).ι :=
  restrictPushforwardIso (mod V) ≪≫ θ V W h ≪≫
    (restrictPushforwardLeIso (coe_le_coe h) (mod W)).symm

/-- **The reduction lemma.** If a family of isomorphisms
`θ h : mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE h)` satisfies the cocycle condition
along a chain of two inclusions — modulo the coherence
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` of the restriction functors — then
the comparisons `AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso` obtained from it satisfy
the cocycle condition of `AlgebraicGeometry.AffineOpensGlue.ChartComparison`.

With this, assembling a glueing datum takes only the cocycle condition for `θ`, which is the
actual mathematics: the pushforwards cancel against each other by
`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso_inv_comp`, and the two ways of
restricting from `W` to `V` agree by
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso_hom_app_comp_inv`. -/
theorem comp_trans_of_restrictIso
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE (coe_le_coe h)))
    (hθ : ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (θ V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (θ V' W h').hom ≫
          (restrictFunctorTransIso (coe_le_coe h) (coe_le_coe h')
            (coe_le_coe (h.trans h'))).hom.app (mod W) =
        (θ V W (h.trans h')).hom)
    (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W) :
    (compOfRestrictIso mod θ V V' h).hom ≫
        restrictLocal (compOfRestrictIso mod θ V' W h').hom (coe_le_coe h) =
      (compOfRestrictIso mod θ V W (h.trans h')).hom := by
  dsimp only [compOfRestrictIso]
  rw [restrictLocal_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [restrictPushforwardLeIso_inv_comp_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← restrictFunctorTransIso_hom_app_comp_inv (coe_le_coe h) (coe_le_coe h')
      (coe_le_coe (h.trans h')) (mod W),
    reassoc_of% hθ V V' W h h']

/-- **The glueing datum built from a family of isomorphisms along the inclusions.** A module on
each affine open of `X`, an isomorphism of the module on `V` with the restriction along `V ⟶ W`
of the module on `W` for each inclusion `V ≤ W`, and the cocycle condition for those, assemble
into an `AlgebraicGeometry.AffineOpensGlue.ChartComparison`, by
`AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso`. -/
def ofRestrictIso
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE (coe_le_coe h)))
    (hθ : ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (θ V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (θ V' W h').hom ≫
          (restrictFunctorTransIso (coe_le_coe h) (coe_le_coe h')
            (coe_le_coe (h.trans h'))).hom.app (mod W) =
        (θ V W (h.trans h')).hom) :
    ChartComparison X where
  mod := mod
  comp {V W} h := compOfRestrictIso mod θ V W h
  comp_trans {V V' W} h h' := comp_trans_of_restrictIso mod θ hθ V V' W h h'

end AlgebraicGeometry.AffineOpensGlue

end
