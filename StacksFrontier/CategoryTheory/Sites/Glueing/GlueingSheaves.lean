module
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Glueing sheaves along a covering

Let `(C, J)` be a site, let `S : C` and let `{f i : X i ⟶ S}` be a covering of `S`. A *glueing
datum for sheaves with respect to this covering* consists of a sheaf `F i` on the slice site
`C/X i` for every `i`, together with isomorphisms `φ i j` between the two restrictions of `F i` and
of `F j` to each overlap of `X i` and `X j` over `S`, subject to the cocycle condition over the
triple overlaps. Every sheaf `F` on `C/S` has its canonical glueing datum, given by the
restrictions `F|_{C/X i}` and the identifications of the two restrictions of `F` to an overlap. The
result of this file is that this construction is essentially surjective: every glueing datum is
isomorphic to the canonical glueing datum of a sheaf `F` on `C/S`, i.e. there are isomorphisms
`φ i : F|_{C/X i} ≅ F i` which are compatible with the `φ i j` over the overlaps. The source writes
the overlaps as the fibre products `X i ×_S X j`; see the implementation notes for the form used
here, which does not assume that they exist.

## Main results

* `CategoryTheory.GrothendieckTopology.essSurj_toDescentData_pseudofunctorOver`: sheaves on the
  slice sites of a covering glue, i.e. the functor from sheaves on `C/S` to glueing data for a
  covering `{X i ⟶ S}` is essentially surjective (Stacks 04TR).

## Implementation notes

Glueing data are `CategoryTheory.Pseudofunctor.DescentData` for the pseudofunctor
`J.pseudofunctorOver A : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, which sends `S` to the category of
`A`-valued sheaves on the slice site `C/S` — the over category `Over S` with the localized
topology `J.over S` — and a morphism `g : S' ⟶ S` to the restriction functor
`J.overMapPullback A g`. The canonical glueing datum of a sheaf is
`Pseudofunctor.toDescentData f`, whose object part is the family of restrictions
`F|_{C/X i}` equipped with the coherence isomorphisms of the pseudofunctor: these are the
identifications the source draws as the identity on the left edge of its square, the two
restrictions of `F` to an overlap being restrictions along the two equal composites
`C/X i ×_S X j → C/X i → C/S` and `C/X i ×_S X j → C/X j → C/S`. An isomorphism in
`DescentData f` between `toDescentData.obj F` and a given glueing datum is precisely a family of
isomorphisms `φ i : F|_{C/X i} ≅ F i` making the source's squares commute
(`DescentData.isoMk`), so essential surjectivity of `toDescentData f` is the assertion of the
source, with the conclusion's `F` and `φ i` as its data.

Two departures from the source's form, both generalizations. First, `DescentData` records the
transition isomorphisms not over chosen fibre products `X i ×_S X j` but over every object `Y`
equipped with morphisms `Y ⟶ X i` and `Y ⟶ X j` agreeing over `S`; the cocycle condition of the
source is `DescentData.hom_comp` and the normalisation `φ i i = id` it leaves implicit is
`DescentData.hom_self`. Writing the overlaps as `U_i ×_U U_j` presupposes that those fibre
products exist, which the definition of a site does not provide; the formulation over an arbitrary
`Y` needs no such assumption, and agrees with the source's whenever they do exist, by
`DescentData'.descentDataEquivalence`. Secondly the sheaves take values in an arbitrary category
`A` rather than in sets; the sections of the glued sheaf over `V/S` are cut out of a limit indexed
by the covering sieve, so `A` is assumed to have limits of that size, and the source's sheaves of
sets are the case `A = Type (max t u v)`.

## References

Stacks Project, tag 04TR (`sites-lemma-glue-sheaves`); tag 04TQ is the full faithfulness of the
same functor and tag 04TS the resulting equivalence of categories.

* [Stacks 04TR](https://stacks.math.columbia.edu/tag/04TR)
-/


namespace CategoryTheory.GrothendieckTopology

section

universe t v' u' v u w
open CategoryTheory Limits
open CategoryTheory Limits Opposite Pseudofunctor.LocallyDiscreteOpToCat

namespace Stacks.SheafGluing.DescentDataEssSurj

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'} [Category.{v'} A]
  {ι : Type t} {S : C} {X : ι → C}

/-! ### The total category of a family of morphisms -/

/-- The object of `C/S` attached to a pair `(i, W)` with `W` an object of `C/X i`. -/
private abbrev totOver (f : ∀ i, X i ⟶ S) (t : Σ i : ι, Over (X i)) : Over S :=
  (Over.map (f t.1)).obj t.2

/-- The total category of a family `f i : X i ⟶ S`: its objects are the pairs `(i, W)` with `W` an
object of `C/X i`, and its morphisms are the morphisms of `C/S` between the associated objects. -/
private abbrev Tot (f : ∀ i, X i ⟶ S) : Type (max t u v) :=
  InducedCategory (Over S) (totOver f)

/-- The projection from the total category of a family to `C/S`. -/
private abbrev totπ (f : ∀ i, X i ⟶ S) : Tot f ⥤ Over S :=
  inducedFunctor (totOver f)

/-- The inclusion of the slice category `C/X i` in the total category of the family. -/
@[implicit_reducible]
private def totι (f : ∀ i, X i ⟶ S) (i : ι) : Over (X i) ⥤ Tot f where
  obj W := ⟨i, W⟩
  map u := InducedCategory.homMk ((Over.map (f i)).map u)
  map_id W :=
    InducedCategory.hom_ext
      (by simp)
  map_comp u v :=
    InducedCategory.hom_ext
      (by simp)

/-- The morphism of the total category between two objects with the same underlying object of `C`,
which is the identity on that object. -/
private def totHom (f : ∀ i, X i ⟶ S) {i₁ i₂ : ι} {W : C} (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂)
    (h : p₁ ≫ f i₁ = p₂ ≫ f i₂) : (totι f i₂).obj (Over.mk p₂) ⟶ (totι f i₁).obj (Over.mk p₁) :=
  InducedCategory.homMk
    (Over.homMk (𝟙 W)
      (show (𝟙 W ≫ (p₁ ≫ f i₁) : W ⟶ S) = p₂ ≫ f i₂ from (Category.id_comp _).trans h))

/-- A morphism of `C` which factors one morphism of `C/Z` through another is itself a morphism of
`C/Z`. -/
private def overLift {Z : C} {a b c : Over Z} (p : a ⟶ c) (q : b ⟶ c) (u : a.left ⟶ b.left)
    (hu : u ≫ q.left = p.left) : a ⟶ b :=
  Over.homMk u (by rw [← Over.w q, ← Category.assoc, hu, Over.w p])

private lemma overLift_comp {Z : C} {a b c : Over Z} (p : a ⟶ c) (q : b ⟶ c) (u : a.left ⟶ b.left)
    (hu : u ≫ q.left = p.left) : overLift p q u hu ≫ q = p :=
  Over.OverMorphism.ext hu

/-- A morphism of the total category with target in the fibre over `X i` lifts along the image of a
morphism `v` of that fibre, once a morphism `u` of `C` witnessing the factorisation is given. -/
private def totLift (f : ∀ i, X i ⟶ S) {i : ι} {W V : Over (X i)} {t : Tot f}
    (g : t ⟶ (totι f i).obj W) (v : V ⟶ W) (u : t.2.left ⟶ V.left) (hu : u ≫ v.left = g.hom.left) :
    t ⟶ (totι f i).obj V :=
  InducedCategory.homMk (overLift g.hom ((Over.map (f i)).map v) u hu)

private lemma totLift_comp (f : ∀ i, X i ⟶ S) {i : ι} {W V : Over (X i)} {t : Tot f}
    (g : t ⟶ (totι f i).obj W) (v : V ⟶ W) (u : t.2.left ⟶ V.left) (hu : u ≫ v.left = g.hom.left) :
    totLift f g v u hu ≫ (totι f i).map v = g :=
  InducedCategory.hom_ext (overLift_comp g.hom ((Over.map (f i)).map v) u hu)

/-- A morphism of the total category with target in the fibre over `X i` factors the image of a
morphism `v` of that fibre, once a morphism `u` of `C` witnessing the factorisation is given. -/
private def totDesc (f : ∀ i, X i ⟶ S) {i : ι} {W V : Over (X i)} {t : Tot f}
    (g : t ⟶ (totι f i).obj W) (v : V ⟶ W) (u : V.left ⟶ t.2.left) (hu : u ≫ g.hom.left = v.left) :
    ((totι f i).obj V : Tot f) ⟶ t :=
  InducedCategory.homMk (overLift ((Over.map (f i)).map v) g.hom u hu)

private lemma totDesc_comp (f : ∀ i, X i ⟶ S) {i : ι} {W V : Over (X i)} {t : Tot f}
    (g : t ⟶ (totι f i).obj W) (v : V ⟶ W) (u : V.left ⟶ t.2.left) (hu : u ≫ g.hom.left = v.left) :
    totDesc f g v u hu ≫ g = (totι f i).map v :=
  InducedCategory.hom_ext (overLift_comp ((Over.map (f i)).map v) g.hom u hu)

/-- A sieve on an object of the fibre over `X i` contains the image of a morphism of that fibre as
soon as it contains a morphism of the total category factoring it. -/
private lemma totι_map_mem (f : ∀ i, X i ⟶ S) {i : ι} {W V : Over (X i)}
    {T : Sieve ((totι f i).obj W)} {t : Tot f} {g : t ⟶ (totι f i).obj W} (hg : T.arrows g)
    (v : V ⟶ W) (u : V.left ⟶ t.2.left) (hu : u ≫ g.hom.left = v.left) :
    T.arrows ((totι f i).map v) := by
  rw [← totDesc_comp f g v u hu]
  exact T.downward_closed hg _

/-- The morphism of the fibre over `X i` with the same underlying morphism of `C` as a given
morphism of the total category into that fibre. -/
private def totFib (f : ∀ i, X i ⟶ S) {i : ι} {W : Over (X i)} {t : Tot f}
    (g : t ⟶ (totι f i).obj W) : (Over.mk (g.hom.left ≫ W.hom) : Over (X i)) ⟶ W :=
  Over.homMk g.hom.left rfl

/-- Every morphism of the total category into the fibre over `X i` factors through the image of a
morphism of that fibre which lies in any sieve containing it: the total category is, over each
fibre, the fibre up to isomorphism. -/
private lemma exists_fac (f : ∀ i, X i ⟶ S) {i : ι} {W : Over (X i)} (T : Sieve ((totι f i).obj W))
    {t : Tot f} {g : t ⟶ (totι f i).obj W} (hg : T.arrows g) :
    ∃ (V : Over (X i)) (v : V ⟶ W) (ε : t ⟶ (totι f i).obj V),
      T.arrows ((totι f i).map v) ∧ ε ≫ (totι f i).map v = g :=
  ⟨Over.mk (g.hom.left ≫ W.hom), totFib f g,
    totLift f g (totFib f g) (𝟙 t.2.left) (Category.id_comp _),
    totι_map_mem f hg (totFib f g) (𝟙 t.2.left) (Category.id_comp _),
    totLift_comp f g (totFib f g) (𝟙 t.2.left) (Category.id_comp _)⟩

/-! ### Sections of sheaves on a slice site -/

/-- The component at `b` of a morphism of sheaves on the slice site `C/Z`. -/
private def app {Z : C} {M N : Sheaf (J.over Z) A} (α : M ⟶ N) (b : Over Z) :
    M.obj.obj (op b) ⟶ N.obj.obj (op b) :=
  α.hom.app (op b)

/-- The components of a composite of morphisms of sheaves. The composite is an argument rather than
the composition of two arguments — in the manner of `Pseudofunctor.mapComp'` — because a morphism
between two values of `J.pseudofunctorOver A` is a composite only up to definitional unfolding of
the composition of `Cat`, which no rewrite sees. -/
private lemma app_comp' {Z : C} {M₁ M₂ M₃ : Sheaf (J.over Z) A} (α : M₁ ⟶ M₂) (β : M₂ ⟶ M₃)
    (γ : M₁ ⟶ M₃) (hγ : α ≫ β = γ) (b : Over Z) : app γ b = app α b ≫ app β b := by
  subst hγ
  simp [app]

/-- The flexible variant of `Category.id_comp` for `app`, in the manner of
`Pseudofunctor.mapId'`. -/
private lemma app_id' {Z : C} {M : Sheaf (J.over Z) A} (γ : M ⟶ M) (hγ : γ = 𝟙 M) (b : Over Z) :
    app γ b = 𝟙 _ := by
  subst hγ
  simp [app]

private lemma app_naturality {Z : C} {M N : Sheaf (J.over Z) A} (α : M ⟶ N) {b b' : Over Z}
    (w : b' ⟶ b) : M.obj.map w.op ≫ app α b' = app α b ≫ N.obj.map w.op :=
  α.hom.naturality w.op

private lemma hom_ext_app {Z : C} {M N : Sheaf (J.over Z) A} (φ ψ : M ⟶ N)
    (h : ∀ {W : C} (p : W ⟶ Z), app φ (Over.mk p) = app ψ (Over.mk p)) : φ = ψ := by
  ext b
  exact h b.unop.hom

/-- Two morphisms of `C/Z` with the same underlying morphism induce the same map on sections. -/
private lemma map_op_congr {Z : C} (M : Sheaf (J.over Z) A) {b₁ b₂ : Over Z} (u v : b₁ ⟶ b₂)
    (h : u.left = v.left) : M.obj.map u.op = M.obj.map v.op := by
  obtain rfl : u = v := by
    ext; exact h
  rfl

/-- The restriction map of a sheaf on the slice site `C/Z` along `u : W' ⟶ W`, from the sections
over `g : W ⟶ Z` to the sections over `ug : W' ⟶ Z`. -/
private def rest {Z : C} (M : Sheaf (J.over Z) A) {W W' : C} (u : W' ⟶ W) (g : W ⟶ Z) (ug : W' ⟶ Z)
    (e : u ≫ g = ug) : M.obj.obj (op (Over.mk g)) ⟶ M.obj.obj (op (Over.mk ug)) :=
  M.obj.map (Over.homMk u e : (Over.mk ug : Over Z) ⟶ Over.mk g).op

private lemma rest_comp {Z : C} (M : Sheaf (J.over Z) A) {W W' W'' : C} (u : W' ⟶ W) (v : W'' ⟶ W')
    (w : W'' ⟶ W) (g : W ⟶ Z) (ug : W' ⟶ Z) (vug : W'' ⟶ Z) (hw : v ≫ u = w) (e : u ≫ g = ug)
    (e' : v ≫ ug = vug) (e'' : w ≫ g = vug) :
    rest M u g ug e ≫ rest M v ug vug e' = rest M w g vug e'' := by
  rw [rest, rest, rest, ← Functor.map_comp, ← op_comp]
  exact map_op_congr M _ _ (by simp [hw])

private lemma rest_eq_map {Z : C} (M : Sheaf (J.over Z) A) {W W' : C} (u : W' ⟶ W) (g : W ⟶ Z)
    (ug : W' ⟶ Z) (e : u ≫ g = ug) (w : (Over.mk ug : Over Z) ⟶ Over.mk g) (hw : w.left = u) :
    rest M u g ug e = M.obj.map w.op := by
  rw [rest]
  exact map_op_congr M _ _ (by simp [hw])

/-! The restriction maps along an identity of `C` are the identifications between the sections over
two objects of `C/Z` with the same underlying object; the three lemmas below are the bookkeeping
they need, and they are used as a local simp set. -/

private lemma rest_id_self {Z : C} (M : Sheaf (J.over Z) A) {W : C} (g : W ⟶ Z) (e : 𝟙 W ≫ g = g) :
    rest M (𝟙 W) g g e = 𝟙 _ := by
  rw [rest, map_op_congr M _ (𝟙 (Over.mk g)) (by simp)]
  simp

private lemma rest_id_comp {Z : C} (M : Sheaf (J.over Z) A) {W : C} (p q r : W ⟶ Z)
    (e : 𝟙 W ≫ p = q) (e' : 𝟙 W ≫ q = r) :
    rest M (𝟙 W) p q e ≫ rest M (𝟙 W) q r e' =
      rest M (𝟙 W) p r
        (by
          subst e; subst e'; simp) :=
  rest_comp M (𝟙 W) (𝟙 W) (𝟙 W) p q r (by simp) e e' _

private lemma rest_id_comp_assoc {Z : C} (M : Sheaf (J.over Z) A) {W : C} (p q r : W ⟶ Z)
    (e : 𝟙 W ≫ p = q) (e' : 𝟙 W ≫ q = r) {a : A} (φ : M.obj.obj (op (Over.mk r)) ⟶ a) :
    rest M (𝟙 W) p q e ≫ rest M (𝟙 W) q r e' ≫ φ =
      rest M (𝟙 W) p r
          (by
            subst e; subst e'; simp) ≫
        φ := by
  rw [← Category.assoc (rest M (𝟙 W) p q e) (rest M (𝟙 W) q r e') φ, rest_id_comp]

attribute [local simp] rest_id_self rest_id_comp rest_id_comp_assoc

/-! ### Components of morphisms between pullbacks of sheaves -/

/-- The restriction of a sheaf on the slice site `C/Z'` to the slice site `C/Z` along `g : Z ⟶ Z'`.
It is reducible: it is the value of the pseudofunctor, presented as a sheaf so that the lemmas
about sections apply to it without unfolding `J.pseudofunctorOver A`. -/
private abbrev pull {Z Z' : C} (g : Z ⟶ Z') (G : Sheaf (J.over Z') A) : Sheaf (J.over Z) A :=
  ((J.pseudofunctorOver A).map g.op.toLoc).toFunctor.obj G

/-- The component at `Over.mk p` of a morphism between the pullbacks of two sheaves along
`g₁ : Y ⟶ Z₁` and `g₂ : Y ⟶ Z₂`, read as a map from the sections of `M₁` over `Over.mk (p ≫ g₁)`
to the sections of `M₂` over `Over.mk (p ≫ g₂)`. -/
private def appS {Z₁ Z₂ Y : C} (M₁ : Sheaf (J.over Z₁) A) (M₂ : Sheaf (J.over Z₂) A) {g₁ : Y ⟶ Z₁}
    {g₂ : Y ⟶ Z₂} (α : pull g₁ M₁ ⟶ pull g₂ M₂) {W : C} (p : W ⟶ Y) :
    M₁.obj.obj (op (Over.mk (p ≫ g₁))) ⟶ M₂.obj.obj (op (Over.mk (p ≫ g₂))) :=
  app α (Over.mk p)

/-- The components of the identity, as `app_id'`. -/
private lemma appS_id' {Z Y : C} (M : Sheaf (J.over Z) A) {g : Y ⟶ Z} (α : pull g M ⟶ pull g M)
    (hα : α = 𝟙 _) {W : C} (p : W ⟶ Y) : appS M M α p = 𝟙 _ :=
  app_id' α hα (Over.mk p)

/-- The components of a composite, as `app_comp'`. -/
private lemma appS_comp' {Z₁ Z₂ Z₃ Y : C} (M₁ : Sheaf (J.over Z₁) A) (M₂ : Sheaf (J.over Z₂) A)
    (M₃ : Sheaf (J.over Z₃) A) {g₁ : Y ⟶ Z₁} {g₂ : Y ⟶ Z₂} {g₃ : Y ⟶ Z₃}
    (α : pull g₁ M₁ ⟶ pull g₂ M₂) (β : pull g₂ M₂ ⟶ pull g₃ M₃) (γ : pull g₁ M₁ ⟶ pull g₃ M₃)
    (hγ : α ≫ β = γ) {W : C} (p : W ⟶ Y) : appS M₁ M₃ γ p = appS M₁ M₂ α p ≫ appS M₂ M₃ β p :=
  app_comp' α β γ hγ (Over.mk p)

private lemma hom_ext_appS {Z₁ Z₂ Y : C} (M₁ : Sheaf (J.over Z₁) A) (M₂ : Sheaf (J.over Z₂) A)
    {g₁ : Y ⟶ Z₁} {g₂ : Y ⟶ Z₂} (φ ψ : pull g₁ M₁ ⟶ pull g₂ M₂)
    (h : ∀ {W : C} (p : W ⟶ Y), appS M₁ M₂ φ p = appS M₁ M₂ ψ p) : φ = ψ :=
  hom_ext_app φ ψ (fun p => h p)

/-- Restriction maps commute with the components of a morphism between pullbacks of sheaves. -/
private lemma rest_appS {Z₁ Z₂ Y : C} (M₁ : Sheaf (J.over Z₁) A) (M₂ : Sheaf (J.over Z₂) A)
    {g₁ : Y ⟶ Z₁} {g₂ : Y ⟶ Z₂} (α : pull g₁ M₁ ⟶ pull g₂ M₂) {W W' : C} (p : W ⟶ Y) (p' : W' ⟶ Y)
    (u : W' ⟶ W) (hu : u ≫ p = p') (e₁ : u ≫ (p ≫ g₁) = p' ≫ g₁) (e₂ : u ≫ (p ≫ g₂) = p' ≫ g₂) :
    rest M₁ u (p ≫ g₁) (p' ≫ g₁) e₁ ≫ appS M₁ M₂ α p' =
      appS M₁ M₂ α p ≫ rest M₂ u (p ≫ g₂) (p' ≫ g₂) e₂ := by
  let w : (Over.mk p' : Over Y) ⟶ Over.mk p := Over.homMk u hu
  rw [rest_eq_map M₁ u _ _ e₁ ((Over.map g₁).map w) rfl,
    rest_eq_map M₂ u _ _ e₂ ((Over.map g₂).map w) rfl]
  exact app_naturality α w

/-! ### The coherence isomorphisms of the pseudofunctor of sheaves on slice sites -/

/-- The coherence isomorphism of `J.pseudofunctorOver A` at a factorisation whose composite is the
composite itself. It is `Pseudofunctor.mapComp'_eq_mapComp` in the syntactic form the coherence
isomorphisms of a `pullHom` take. -/
private lemma mapComp'_eq {Z₁ Y Y' : C} (g : Y ⟶ Z₁) (a : Y' ⟶ Y) :
    (J.pseudofunctorOver A).mapComp' g.op.toLoc a.op.toLoc (a ≫ g).op.toLoc (by grind) =
      (J.pseudofunctorOver A).mapComp g.op.toLoc a.op.toLoc :=
  Pseudofunctor.mapComp'_eq_mapComp (F := J.pseudofunctorOver A) g.op.toLoc a.op.toLoc

/-- The components of the coherence isomorphism of `J.pseudofunctorOver A`. -/
private lemma mapComp'_hom_app {Z₁ Y Y' W : C} (g : Y ⟶ Z₁) (a : Y' ⟶ Y) (ag : Y' ⟶ Z₁)
    (hag : a ≫ g = ag) (M : Sheaf (J.over Z₁) A) (p : W ⟶ Y') :
    app
        (((J.pseudofunctorOver A).mapComp' g.op.toLoc a.op.toLoc ag.op.toLoc
              (by grind)).hom.toNatTrans.app
          M)
        (Over.mk p) =
      rest M (𝟙 W) (p ≫ ag) ((p ≫ a) ≫ g)
        (by
          rw [← hag]; simp) := by
  subst hag
  simp only [app, rest]
  rw [mapComp'_eq, GrothendieckTopology.pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app]
  exact map_op_congr M _ _ (by simp)

/-- The components of the inverse of the coherence isomorphism of `J.pseudofunctorOver A`. -/
private lemma mapComp'_inv_app {Z₁ Y Y' W : C} (g : Y ⟶ Z₁) (a : Y' ⟶ Y) (ag : Y' ⟶ Z₁)
    (hag : a ≫ g = ag) (M : Sheaf (J.over Z₁) A) (p : W ⟶ Y') :
    app
        (((J.pseudofunctorOver A).mapComp' g.op.toLoc a.op.toLoc ag.op.toLoc
              (by grind)).inv.toNatTrans.app
          M)
        (Over.mk p) =
      rest M (𝟙 W) ((p ≫ a) ≫ g) (p ≫ ag)
        (by
          rw [← hag]; simp) := by
  subst hag
  simp only [app, rest]
  rw [mapComp'_eq, GrothendieckTopology.pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app]
  exact map_op_congr M _ _ (by simp)

/-- The components of a pullback of a morphism between pullbacks of sheaves. -/
private lemma appS_pullHom {Z₁ Z₂ Y Y' W : C} (M₁ : Sheaf (J.over Z₁) A) (M₂ : Sheaf (J.over Z₂) A)
    {g₁ : Y ⟶ Z₁} {g₂ : Y ⟶ Z₂} (α : pull g₁ M₁ ⟶ pull g₂ M₂) (a : Y' ⟶ Y) (ag₁ : Y' ⟶ Z₁)
    (ag₂ : Y' ⟶ Z₂) (h₁ : a ≫ g₁ = ag₁) (h₂ : a ≫ g₂ = ag₂) (p : W ⟶ Y') :
    appS M₁ M₂ (pullHom α a ag₁ ag₂ h₁ h₂) p =
      rest M₁ (𝟙 W) (p ≫ ag₁) ((p ≫ a) ≫ g₁)
          (by
            rw [← h₁]; simp) ≫
        appS M₁ M₂ α (p ≫ a) ≫
        rest M₂ (𝟙 W) ((p ≫ a) ≫ g₂) (p ≫ ag₂)
          (by
            rw [← h₂]; simp) := by
  simp only [appS]
  rw [app_comp'
      (((J.pseudofunctorOver A).mapComp' g₁.op.toLoc a.op.toLoc ag₁.op.toLoc
            (by grind)).hom.toNatTrans.app
        M₁)
      (((J.pseudofunctorOver A).map a.op.toLoc).toFunctor.map α ≫
        ((J.pseudofunctorOver A).mapComp' g₂.op.toLoc a.op.toLoc ag₂.op.toLoc
              (by grind)).inv.toNatTrans.app
          M₂)
      (pullHom α a ag₁ ag₂ h₁ h₂) rfl (Over.mk p),
    app_comp' (((J.pseudofunctorOver A).map a.op.toLoc).toFunctor.map α)
      (((J.pseudofunctorOver A).mapComp' g₂.op.toLoc a.op.toLoc ag₂.op.toLoc
            (by grind)).inv.toNatTrans.app
        M₂)
      _ rfl (Over.mk p),
    mapComp'_hom_app g₁ a ag₁ h₁ M₁ p, mapComp'_inv_app g₂ a ag₂ h₂ M₂ p]
  exact rfl

/-! ### The comparison maps of a glueing datum -/

/-- The sheaf on the slice site `C/X i` underlying a glueing datum. It is reducible: it is the
value of the pseudofunctor, presented as a sheaf so that the lemmas about sections apply to it
without unfolding `J.pseudofunctorOver A`. -/
private abbrev sh {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) (i : ι) :
    Sheaf (J.over (X i)) A :=
  D.obj i

/-- The transition morphisms of a glueing datum do not depend on the morphism to `S` that the two
morphisms of the family are required to agree over. -/
private lemma hom_congr {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    (q q' : Y ⟶ S) {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (h₁ : g₁ ≫ f i₁ = q)
    (h₂ : g₂ ≫ f i₂ = q) (h₁' : g₁ ≫ f i₁ = q') (h₂' : g₂ ≫ f i₂ = q') :
    D.hom q g₁ g₂ h₁ h₂ = D.hom q' g₁ g₂ h₁' h₂' := by
  obtain rfl : q = q' := by rw [← h₁, h₁']
  rfl

/-- The transition morphisms of a glueing datum are compatible with pullback: the one attached to
the two morphisms `a ≫ g₁` and `a ≫ g₂` is the pullback along `a` of the one attached to `g₁` and
`g₂`. This is `Pseudofunctor.DescentData.pullHom_hom`, with the morphism to `S` that the two
composites are read over left implicit. -/
private lemma hom_eq_pullHom {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {Y Z : C} (a : Z ⟶ Y) (q : Y ⟶ S) {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂)
    (h₁ : g₁ ≫ f i₁ = q) (h₂ : g₂ ≫ f i₂ = q) (ag₁ : Z ⟶ X i₁) (ag₂ : Z ⟶ X i₂) (e₁ : a ≫ g₁ = ag₁)
    (e₂ : a ≫ g₂ = ag₂) (h : ag₁ ≫ f i₁ = ag₂ ≫ f i₂) :
    D.hom (ag₁ ≫ f i₁) ag₁ ag₂ rfl h.symm = pullHom (D.hom q g₁ g₂ h₁ h₂) a ag₁ ag₂ e₁ e₂ :=
  (hom_congr D (ag₁ ≫ f i₁) (a ≫ q) ag₁ ag₂ rfl h.symm
        (by
          rw [← e₁, ← h₁]; simp)
        (by
          rw [← e₂, ← h₂]; simp)).trans
    (D.pullHom_hom a q (a ≫ q) rfl g₁ g₂ h₁ h₂ ag₁ ag₂ e₁ e₂).symm

/-- The comparison map of a glueing datum on sections: if `g₁ : Y ⟶ X i₁` and `g₂ : Y ⟶ X i₂` lie
over the same morphism `Y ⟶ S`, this is the induced map from the sections of `F i₁` over `(Y, g₁)`
to the sections of `F i₂` over `(Y, g₂)`. -/
private def trans {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (h : g₁ ≫ f i₁ = g₂ ≫ f i₂) :
    (sh D i₁).obj.obj (op (Over.mk g₁)) ⟶ (sh D i₂).obj.obj (op (Over.mk g₂)) :=
  rest (sh D i₁) (𝟙 Y) g₁ (𝟙 Y ≫ g₁) rfl ≫
    appS (sh D i₁) (sh D i₂) (D.hom (g₁ ≫ f i₁) g₁ g₂ rfl h.symm) (𝟙 Y) ≫
    rest (sh D i₂) (𝟙 Y) (𝟙 Y ≫ g₂) g₂ (by simp)

/-- The components of a transition morphism of a glueing datum are the comparison maps. -/
private lemma appS_hom {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    (q : Y ⟶ S) {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (h₁ : g₁ ≫ f i₁ = q)
    (h₂ : g₂ ≫ f i₂ = q) {W : C} (p : W ⟶ Y) (h' : (p ≫ g₁) ≫ f i₁ = (p ≫ g₂) ≫ f i₂) :
    appS (sh D i₁) (sh D i₂) (D.hom q g₁ g₂ h₁ h₂) p = trans D (p ≫ g₁) (p ≫ g₂) h' := by
  rw [trans, hom_eq_pullHom D p q g₁ g₂ h₁ h₂ (p ≫ g₁) (p ≫ g₂) rfl rfl h',
    appS_pullHom (sh D i₁) (sh D i₂) (D.hom q g₁ g₂ h₁ h₂) p (p ≫ g₁) (p ≫ g₂) rfl rfl (𝟙 W)]
  simp only [Category.assoc, rest_id_comp, rest_id_comp_assoc]
  rw [reassoc_of%
      (rest_appS (sh D i₁) (sh D i₂) (D.hom q g₁ g₂ h₁ h₂) p (𝟙 W ≫ p) (𝟙 W) rfl (by simp)
        (by simp))]
  simp [rest_id_self, rest_id_comp]

/-- The normalisation of the comparison maps: the one attached to a morphism and itself is the
identity. -/
private lemma trans_self {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    {i : ι} (g : Y ⟶ X i) (h : g ≫ f i = g ≫ f i) : trans D g g h = 𝟙 _ := by
  rw [trans, appS_id' (sh D i) (D.hom (g ≫ f i) g g rfl h.symm) (D.hom_self (g ≫ f i) g rfl) (𝟙 Y),
    Category.id_comp (rest (sh D i) (𝟙 Y) (𝟙 Y ≫ g) g (by simp)), rest_id_comp, rest_id_self]

/-- The cocycle condition on the comparison maps: three morphisms over the same morphism to `S`
give a commuting triangle. -/
private lemma trans_trans {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    {i₁ i₂ i₃ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (g₃ : Y ⟶ X i₃) (h₁₂ : g₁ ≫ f i₁ = g₂ ≫ f i₂)
    (h₂₃ : g₂ ≫ f i₂ = g₃ ≫ f i₃) (h₁₃ : g₁ ≫ f i₁ = g₃ ≫ f i₃) :
    trans D g₁ g₂ h₁₂ ≫ trans D g₂ g₃ h₂₃ = trans D g₁ g₃ h₁₃ := by
  have hmid :
    appS (sh D i₂) (sh D i₃) (D.hom (g₂ ≫ f i₂) g₂ g₃ rfl h₂₃.symm) (𝟙 Y) =
      appS (sh D i₂) (sh D i₃) (D.hom (g₁ ≫ f i₁) g₂ g₃ h₁₂.symm h₁₃.symm) (𝟙 Y) :=
    congrArg (fun γ => appS (sh D i₂) (sh D i₃) γ (𝟙 Y))
      (hom_congr D (g₂ ≫ f i₂) (g₁ ≫ f i₁) g₂ g₃ rfl h₂₃.symm h₁₂.symm h₁₃.symm)
  simp only [trans, Category.assoc]
  rw [hmid]
  simp only [rest_id_comp_assoc, rest_id_self, Category.id_comp]
  rw [←
    reassoc_of%
      (appS_comp' (sh D i₁) (sh D i₂) (sh D i₃) (D.hom (g₁ ≫ f i₁) g₁ g₂ rfl h₁₂.symm)
        (D.hom (g₁ ≫ f i₁) g₂ g₃ h₁₂.symm h₁₃.symm) (D.hom (g₁ ≫ f i₁) g₁ g₃ rfl h₁₃.symm)
        (D.hom_comp (g₁ ≫ f i₁) g₁ g₂ g₃ rfl h₁₂.symm h₁₃.symm) (𝟙 Y))]

/-- The comparison map attached to two equal morphisms into the same member of the family is the
restriction map of that member along the identity. -/
private lemma trans_eq_rest {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    {i : ι} (g₁ g₂ : Y ⟶ X i) (h : g₁ ≫ f i = g₂ ≫ f i) (e : 𝟙 Y ≫ g₁ = g₂) :
    trans D g₁ g₂ h = rest (sh D i) (𝟙 Y) g₁ g₂ e := by
  obtain rfl : g₁ = g₂ := by rw [← e, Category.id_comp]
  rw [trans_self D g₁ h, rest_id_self]

/-- A comparison map absorbs the restriction map along an identity of `C` preceding it. -/
private lemma rest_id_trans {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y : C}
    {i₁ i₂ : ι} (g₁ g₁' : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (e : 𝟙 Y ≫ g₁ = g₁')
    (h : g₁ ≫ f i₁ = g₂ ≫ f i₂) (h' : g₁' ≫ f i₁ = g₂ ≫ f i₂) :
    rest (sh D i₁) (𝟙 Y) g₁ g₁' e ≫ trans D g₁' g₂ h' = trans D g₁ g₂ h := by
  rw [←
    trans_eq_rest D g₁ g₁'
      (by
        rw [← e]; simp)
      e]
  exact trans_trans D g₁ g₁' g₂ _ h' h

/-- The comparison maps are compatible with the restriction maps. -/
private lemma rest_trans {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) {Y Z : C}
    (a : Z ⟶ Y) {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (ag₁ : Z ⟶ X i₁) (ag₂ : Z ⟶ X i₂)
    (e₁ : a ≫ g₁ = ag₁) (e₂ : a ≫ g₂ = ag₂) (h : g₁ ≫ f i₁ = g₂ ≫ f i₂)
    (h' : ag₁ ≫ f i₁ = ag₂ ≫ f i₂) :
    rest (sh D i₁) a g₁ ag₁ e₁ ≫ trans D ag₁ ag₂ h' =
      trans D g₁ g₂ h ≫ rest (sh D i₂) a g₂ ag₂ e₂ := by
  simp only [trans]
  rw [hom_eq_pullHom D a (g₁ ≫ f i₁) g₁ g₂ rfl h.symm ag₁ ag₂ e₁ e₂ h',
    appS_pullHom (sh D i₁) (sh D i₂) (D.hom (g₁ ≫ f i₁) g₁ g₂ rfl h.symm) a ag₁ ag₂ e₁ e₂ (𝟙 Z)]
  simp only [Category.assoc, rest_id_comp, rest_id_comp_assoc]
  rw [reassoc_of%
      (rest_comp (sh D i₁) a (𝟙 Z) a g₁ ag₁ ((𝟙 Z ≫ a) ≫ g₁) (by simp) e₁
        (by
          rw [← e₁]; simp)
        (by simp)),
    ←
    reassoc_of%
      (rest_comp (sh D i₁) (𝟙 Y) a a g₁ (𝟙 Y ≫ g₁) ((𝟙 Z ≫ a) ≫ g₁) (by simp) rfl (by simp)
        (by simp)),
    reassoc_of%
      (rest_appS (sh D i₁) (sh D i₂) (D.hom (g₁ ≫ f i₁) g₁ g₂ rfl h.symm) (𝟙 Y) (𝟙 Z ≫ a) a
        (by simp) (by simp) (by simp)),
    rest_comp (sh D i₂) a (𝟙 Z) a (𝟙 Y ≫ g₂) ((𝟙 Z ≫ a) ≫ g₂) ag₂ (by simp) (by simp)
      (by
        rw [← e₂]; simp)
      (by simp [e₂]),
    rest_comp (sh D i₂) (𝟙 Y) a a (𝟙 Y ≫ g₂) g₂ ag₂ (by simp) (by simp) e₂ (by simp [e₂])]

/-! ### The presheaf on the total category attached to a glueing datum -/

/-- The restriction map of the presheaf attached to a glueing datum. -/
private def totPresheafMap {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i₁ i₂ : ι} (W₁ : Over (X i₁)) (W₂ : Over (X i₂)) (a : W₂.left ⟶ W₁.left)
    (h : (a ≫ W₁.hom) ≫ f i₁ = W₂.hom ≫ f i₂) :
    (sh D i₁).obj.obj (op W₁) ⟶ (sh D i₂).obj.obj (op W₂) :=
  rest (sh D i₁) a W₁.hom (a ≫ W₁.hom) rfl ≫ trans D (a ≫ W₁.hom) W₂.hom h

private lemma totPresheafMap_eq_id {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i : ι} (W : Over (X i)) (a : W.left ⟶ W.left) (h) (ha : a = 𝟙 W.left) :
    totPresheafMap D W W a h = 𝟙 _ := by
  subst ha
  exact (rest_id_trans D W.hom (𝟙 W.left ≫ W.hom) W.hom rfl rfl h).trans (trans_self D W.hom rfl)

private lemma totPresheafMap_comp {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i₁ i₂ i₃ : ι} (W₁ : Over (X i₁)) (W₂ : Over (X i₂)) (W₃ : Over (X i₃)) (a : W₂.left ⟶ W₁.left)
    (b : W₃.left ⟶ W₂.left) (c : W₃.left ⟶ W₁.left) (hc : b ≫ a = c) (h₁ h₂ h₃) :
    totPresheafMap D W₁ W₃ c h₃ = totPresheafMap D W₁ W₂ a h₁ ≫ totPresheafMap D W₂ W₃ b h₂ := by
  have hmid : (c ≫ W₁.hom) ≫ f i₁ = (b ≫ W₂.hom) ≫ f i₂ := by
    rw [← hc, Category.assoc, Category.assoc, Category.assoc, ← Category.assoc a W₁.hom (f i₁), h₁]
  rw [totPresheafMap, totPresheafMap, totPresheafMap]
  simp only [Category.assoc]
  rw [←
    reassoc_of%
      (rest_trans D b (a ≫ W₁.hom) W₂.hom (c ≫ W₁.hom) (b ≫ W₂.hom)
        (by
          rw [← hc]; simp)
        rfl h₁ hmid),
    reassoc_of%
      (rest_comp (sh D i₁) a b c W₁.hom (a ≫ W₁.hom) (c ≫ W₁.hom) hc rfl
        (by
          rw [← hc]; simp)
        rfl),
    trans_trans D (c ≫ W₁.hom) (b ≫ W₂.hom) W₃.hom hmid h₂ h₃]

/-- The presheaf on the total category attached to a glueing datum: its sections over `(i, W)` are
the sections of `F i` over `W`. -/
@[implicit_reducible, ega "0 3.3.1" "partial"]
private def totPresheaf {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f) :
    (Tot f)ᵒᵖ ⥤ A
    where
  obj t := (sh D t.unop.1).obj.obj (op t.unop.2)
  map {t₁ t₂} u :=
    totPresheafMap D t₁.unop.2 t₂.unop.2 u.unop.hom.left
      (by simpa [totOver] using Over.w u.unop.hom)
  map_id t := totPresheafMap_eq_id D _ _ _ rfl
  map_comp u v := totPresheafMap_comp D _ _ _ _ _ _ rfl _ _ _

private lemma totPresheaf_map {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {t₁ t₂ : (Tot f)ᵒᵖ} (u : t₁ ⟶ t₂) :
    (totPresheaf D).map u =
      totPresheafMap D t₁.unop.2 t₂.unop.2 u.unop.hom.left
        (by simpa [totOver] using Over.w u.unop.hom) :=
  rfl

/-- On the fibre over `X i`, the presheaf attached to a glueing datum is `F i`. -/
private lemma totPresheafMap_fiber {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i : ι} {W W' : Over (X i)} (w : W' ⟶ W) (a : W'.left ⟶ W.left) (ha : a = w.left) (h) :
    totPresheafMap D W W' a h = (sh D i).obj.map w.op := by
  have hw : a ≫ W.hom = W'.hom := by
    rw [ha]; exact Over.w w
  rw [totPresheafMap,
    trans_eq_rest D (a ≫ W.hom) W'.hom h
      (by
        rw [hw]; simp),
    rest_comp (sh D i) a (𝟙 W'.left) a W.hom (a ≫ W.hom) W'.hom (by simp) rfl
      (by
        rw [hw]; simp)
      hw]
  exact rest_eq_map (sh D i) a W.hom W'.hom hw w ha.symm

/-- The restriction map of the presheaf attached to a glueing datum, along a morphism which is the
identity on the underlying object, is the comparison map. -/
private lemma totPresheafMap_eq_trans {f : ∀ i, X i ⟶ S}
    (D : (J.pseudofunctorOver A).DescentData f) {i₁ i₂ : ι} {W : C} (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂)
    (a : (Over.mk p₂).left ⟶ (Over.mk p₁).left) (ha : a = 𝟙 W) (h) (h' : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    totPresheafMap D (Over.mk p₁) (Over.mk p₂) a h = trans D p₁ p₂ h' := by
  subst ha
  exact rest_id_trans D p₁ (𝟙 W ≫ p₁) p₂ rfl h' h

private lemma totPresheaf_map_totHom {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i₁ i₂ : ι} {W : C} (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (h' : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    (totPresheaf D).map (totHom f p₁ p₂ h').op = trans D p₁ p₂ h' := by
  rw [totPresheaf_map]
  exact totPresheafMap_eq_trans D p₁ p₂ _ rfl _ h'

/-- On the fibre over `X i`, the restriction maps of the presheaf attached to a glueing datum are
those of `F i`. -/
private lemma totPresheaf_map_totι {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    {i : ι} {V V' : Over (X i)} (v : V' ⟶ V) :
    (totPresheaf D).map ((totι f i).map v).op = (sh D i).obj.map v.op := by
  rw [totPresheaf_map]
  exact totPresheafMap_fiber D v _ rfl _

/-- The restriction of the presheaf attached to a glueing datum to the fibre over `X i` is
`F i`. -/
private def totPresheafFiberIso {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (i : ι) : (totι f i).op ⋙ totPresheaf D ≅ (sh D i).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun {W₁ W₂} w => by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact totPresheaf_map_totι D w.unop)

/-! ### The glued sheaf -/

/-- The projection from the total category is cover dense when the family is a covering. -/
private lemma isCoverDense_totπ (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows X f ∈ J S) :
    (totπ f).IsCoverDense (J.over S)
    where
  is_cover V := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ (J.pullback_stable V.hom hf)
    intro Z g hg
    obtain ⟨W, a, c, ⟨i⟩, fac⟩ := hg
    rw [Sieve.overEquiv_iff]
    exact
      ⟨{  obj := ⟨i, Over.mk a⟩
          lift := Over.homMk (𝟙 Z) (by simpa [totOver] using fac)
          map := Over.homMk g (by simpa [totOver] using fac.symm)
          fac := by
            ext; exact Category.id_comp g }⟩

/-- A sieve of the total category covering an object of the fibre over `X i` restricts to a
covering sieve of that object in the slice site `C/X i`. -/
private lemma functorPullback_mem (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows X f ∈ J S) (i : ι)
    (W : Over (X i)) (T : Sieve ((totι f i).obj W))
    (hT : T ∈ (totπ f).restrictedTopology (J.over S) ((totι f i).obj W)) :
    T.functorPullback (totι f i) ∈ (J.over (X i)) W := by
  have := isCoverDense_totπ f hf
  have hT' :
    Sieve.overEquiv ((totπ f).obj ((totι f i).obj W)) (T.functorPushforward (totπ f)) ∈ J W.left :=
    Functor.mem_restrictedTopology_iff.1 hT
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ hT'
  intro Z a ha
  replace ha := (Sieve.overEquiv_iff _ _).1 ha
  obtain ⟨t', h, k, hh, fac⟩ := ha
  refine (Sieve.overEquiv_iff _ _).2 ?_
  rw [Sieve.functorPullback_apply]
  refine totι_map_mem f hh _ k.left ?_
  simpa using (congrArg Over.Hom.left fac).symm

/-- **The comparison lemma for the total category of a covering.** A presheaf of types on the total
category whose restriction to every fibre is a sheaf is a sheaf for the topology restricted from
`C/S`. -/
private lemma isSheaf_of_isSheaf_totι {f : ∀ i, X i ⟶ S} (hf : Sieve.ofArrows X f ∈ J S)
    (P : (Tot f)ᵒᵖ ⥤ Type w) (hP : ∀ i : ι, Presieve.IsSheaf (J.over (X i)) ((totι f i).op ⋙ P)) :
    Presieve.IsSheaf ((totπ f).restrictedTopology (J.over S)) P := by
  intro t T hT
  obtain ⟨i, W⟩ := t
  intro x hx
  obtain ⟨s, hs, huniq⟩ :=
    hP i (T.functorPullback (totι f i)) (functorPullback_mem f hf i W T hT)
      (fun ⦃V⦄ v hv => x ((totι f i).map v) hv)
      (by
        intro V₁ V₂ Z u₁ u₂ v₁ v₂ h₁ h₂ hcomm
        have hcomm' :
          (totι f i).map u₁ ≫ (totι f i).map v₁ = (totι f i).map u₂ ≫ (totι f i).map v₂ := by
          rw [← Functor.map_comp, ← Functor.map_comp, hcomm]
        exact hx ((totι f i).map u₁) ((totι f i).map u₂) h₁ h₂ hcomm')
  refine ⟨s, ?_, ?_⟩
  · intro t' g hg
    obtain ⟨V, v, ε, hv, hε⟩ := exists_fac f T hg
    have h1 : P.map ((totι f i).map v).op s = x ((totι f i).map v) hv := hs v hv
    have h2 : x g hg = P.map ε.op (x ((totι f i).map v) hv) := by
      simpa using hx (𝟙 t') ε hg hv ((Category.id_comp g).trans hε.symm)
    have h3 : P.map (ε ≫ (totι f i).map v).op s = P.map g.op s :=
      congrArg (fun (m : t' ⟶ (totι f i).obj W) => P.map m.op s) hε
    rw [h2, ← h1, ← h3, op_comp, Functor.map_comp_apply]
  · exact fun z hz => huniq z fun V v hv => hz ((totι f i).map v) hv

/-- The presheaf attached to a glueing datum is a sheaf for the topology induced on the total
category. -/
@[ega "0 3.3.1" "partial"]
private lemma isSheaf_totPresheaf {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (hf : Sieve.ofArrows X f ∈ J S) :
    Presheaf.IsSheaf ((totπ f).restrictedTopology (J.over S)) (totPresheaf D) := fun E =>
  isSheaf_of_isSheaf_totι hf _ fun i =>
    Presieve.isSheaf_iso _
      (Functor.isoWhiskerRight (totPresheafFiberIso D i) (coyoneda.obj (op E))).symm
      ((sh D i).property E)

variable (A) in
/-- The sheaf on `C/S` glued from a glueing datum. -/
@[ega "0 3.3.1" "more general"]
private noncomputable def glued {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] : Sheaf (J.over S) A :=
  haveI := isCoverDense_totπ f hf
  ((totπ f).sheafPushforwardContinuous A ((totπ f).restrictedTopology (J.over S))
        (J.over S)).objPreimage
    ⟨totPresheaf D, isSheaf_totPresheaf D hf⟩

/-- The restriction of the glued sheaf to the total category is the presheaf attached to the
glueing datum. -/
private noncomputable def gluedIso {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] :
    (totπ f).op ⋙ (glued A D hf).obj ≅ totPresheaf D :=
  haveI := isCoverDense_totπ f hf
  (sheafToPresheaf ((totπ f).restrictedTopology (J.over S)) A).mapIso
    (Functor.objObjPreimageIso
      ((totπ f).sheafPushforwardContinuous A ((totπ f).restrictedTopology (J.over S)) (J.over S))
      ⟨totPresheaf D, isSheaf_totPresheaf D hf⟩)

variable (A) in
/-- The isomorphism between the restriction of the glued sheaf to `C/X i` and `F i`. -/
private noncomputable def gluedFiberIso {f : ∀ i, X i ⟶ S}
    (D : (J.pseudofunctorOver A).DescentData f) (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] (i : ι) :
    pull (f i) (glued A D hf) ≅ sh D i :=
  (fullyFaithfulSheafToPresheaf (J.over (X i)) A).preimageIso
    (Functor.isoWhiskerLeft (totι f i).op (gluedIso D hf) ≪≫ totPresheafFiberIso D i)

private lemma app_gluedFiberIso {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] (i : ι)
    (W : Over (X i)) :
    app (gluedFiberIso A D hf i).hom W = (gluedIso D hf).hom.app (op ((totι f i).obj W)) :=
  Category.comp_id _

/-- **The glueing is compatible with the comparison maps.** Let `W` be an object of `C` with two
morphisms `p₁ : W ⟶ X i₁` and `p₂ : W ⟶ X i₂` agreeing over `S`. Then the isomorphisms between the
restrictions of the glued sheaf and the members of the glueing datum carry the identification of
the sections of the glued sheaf over the two equal composites `W ⟶ X i₁ ⟶ S` and `W ⟶ X i₂ ⟶ S` to
the comparison map of the glueing datum. -/
private lemma app_gluedFiberIso_comp_trans {f : ∀ i, X i ⟶ S}
    (D : (J.pseudofunctorOver A).DescentData f) (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] {i₁ i₂ : ι} {W : C}
    (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (h : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    app (gluedFiberIso A D hf i₁).hom (Over.mk p₁) ≫ trans D p₁ p₂ h =
      rest (glued A D hf) (𝟙 W) (p₁ ≫ f i₁) (p₂ ≫ f i₂) ((Category.id_comp _).trans h) ≫
        app (gluedFiberIso A D hf i₂).hom (Over.mk p₂) := by
  rw [app_gluedFiberIso, app_gluedFiberIso, ← totPresheaf_map_totHom D p₁ p₂ h,
    rest_eq_map (glued A D hf) (𝟙 W) (p₁ ≫ f i₁) (p₂ ≫ f i₂) _ ((totπ f).map (totHom f p₁ p₂ h))
      rfl]
  exact ((gluedIso D hf).hom.naturality (totHom f p₁ p₂ h).op).symm

/-- The components of the canonical glueing datum of the glued sheaf. -/
private lemma appS_ofObj_hom {f : ∀ i, X i ⟶ S} (G : Sheaf (J.over S) A) {Y : C} (q : Y ⟶ S)
    {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (h₁ : g₁ ≫ f i₁ = q) (h₂ : g₂ ≫ f i₂ = q) {W : C}
    (p : W ⟶ Y) :
    appS (pull (f i₁) G) (pull (f i₂) G)
        ((Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver A) (f := f) G).hom q g₁ g₂ h₁
          h₂)
        p =
      rest G (𝟙 W) ((p ≫ g₁) ≫ f i₁) ((p ≫ g₂) ≫ f i₂)
        (by simp [h₁, h₂]) := by
  refine (app_comp' _ _ _ rfl (Over.mk p)).trans ?_
  rw [mapComp'_inv_app (f i₁) g₁ q h₁ G p, mapComp'_hom_app (f i₂) g₂ q h₂ G p]
  exact rest_comp G (𝟙 W) (𝟙 W) (𝟙 W) ((p ≫ g₁) ≫ f i₁) (p ≫ q) ((p ≫ g₂) ≫ f i₂) (by simp) _ _ _

/-- The canonical glueing datum of the glued sheaf is the given glueing datum. -/
@[ega "0 3.3.1" "more general"]
private noncomputable def descentIso {f : ∀ i, X i ⟶ S} (D : (J.pseudofunctorOver A).DescentData f)
    (hf : Sieve.ofArrows X f ∈ J S)
    [∀ V : (Over S)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (totπ f).op) A] :
    ((J.pseudofunctorOver A).toDescentData f).obj (glued A D hf) ≅ D :=
  Pseudofunctor.DescentData.isoMk (gluedFiberIso A D hf)
    (by
      intro Y q i₁ i₂ g₁ g₂ h₁ h₂
      refine hom_ext_appS (pull (f i₁) (glued A D hf)) (sh D i₂) _ _ (fun {W} p => ?_)
      have hcomm : (p ≫ g₁) ≫ f i₁ = (p ≫ g₂) ≫ f i₂ := by
        rw [Category.assoc, Category.assoc, h₁, h₂]
      refine
        (appS_comp' (pull (f i₁) (glued A D hf)) (sh D i₁) (sh D i₂) _ _ _ rfl p).trans
          (Eq.trans ?_
            (appS_comp' (pull (f i₁) (glued A D hf)) (pull (f i₂) (glued A D hf)) (sh D i₂)
                ((Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver A) (f := f)
                      (glued A D hf)).hom
                  q g₁ g₂ h₁ h₂)
                _ _ rfl p).symm)
      rw [appS_hom D q g₁ g₂ h₁ h₂ p hcomm, appS_ofObj_hom (f := f) (glued A D hf) q g₁ g₂ h₁ h₂ p]
      exact app_gluedFiberIso_comp_trans D hf (p ≫ g₁) (p ≫ g₂) hcomm)

end

end Stacks.SheafGluing.DescentDataEssSurj

attribute [local simp] Stacks.SheafGluing.DescentDataEssSurj.rest_id_self
    Stacks.SheafGluing.DescentDataEssSurj.rest_id_comp
  Stacks.SheafGluing.DescentDataEssSurj.rest_id_comp_assoc

@[expose] public section

open Stacks.SheafGluing.DescentDataEssSurj in
/-- **Glueing sheaves.** Let `(C, J)` be a site, let `{f i : X i ⟶ S}` be a covering of an object
`S` of `C`, and let `A` be a category with limits of the relevant size. Then every glueing datum
for `A`-valued sheaves with respect to `{f i : X i ⟶ S}` — a sheaf `F i` on each slice site
`C/X i` together with isomorphisms between the restrictions of `F i` and of `F j` over the
overlaps, satisfying the cocycle condition over the triple overlaps — is isomorphic to the
canonical glueing datum of a sheaf `F` on the slice site `C/S`, i.e. there exists such an `F`
together with isomorphisms `F|_{C/X i} ≅ F i` compatible with the given ones over the overlaps. -/
@[stacks 04TR]
public theorem essSurj_toDescentData_pseudofunctorOver {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A]
    [HasLimitsOfSize.{max t u v, max t u v} A] {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hf : Sieve.ofArrows X f ∈ J S) : ((J.pseudofunctorOver A).toDescentData f).EssSurj := by
  have : HasLimitsOfSize.{v, max t u v} A := hasLimitsOfSizeShrink A
  exact { mem_essImage := fun D => ⟨glued A D hf, ⟨descentIso D hf⟩⟩ }

end

end

end CategoryTheory.GrothendieckTopology

/-! # Sheaves on a slice site are equivalent to glueing data

Let `(C, J)` be a site, let `S : C` and let `{f i : X i ⟶ S}` be a covering of `S`. A *glueing
datum for sheaves with respect to this covering* consists of a sheaf `F i` on each slice site
`C/X i`, together with isomorphisms between the two restrictions of `F i` and of `F j` to each
overlap of `X i` and `X j` over `S`, subject to the cocycle condition over the triple overlaps;
morphisms of glueing data are families of morphisms `F i ⟶ G i` commuting with those
isomorphisms. Every sheaf `F` on the slice site `C/S` has its canonical glueing datum, given by the
restrictions `F|_{C/X i}` together with the canonical identifications of the two restrictions of
`F` to an overlap, and this construction is functorial. The result of this file is that this
functor is an equivalence: sheaves on `C/S` are the same thing as glueing data for the covering.
It is the conjunction of the two halves proved separately, that the functor is fully faithful
(maps of sheaves glue, Stacks 04TQ) and that it is essentially surjective (sheaves glue,
Stacks 04TR).

## Main results

* `CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`: the category
  of `A`-valued sheaves on the slice site `C/S` is equivalent to the category of glueing data for a
  covering `{f i : X i ⟶ S}`, via the functor sending a sheaf to its canonical glueing datum
  (Stacks 04TS).

## Implementation notes

Glueing data are `CategoryTheory.Pseudofunctor.DescentData` for the pseudofunctor
`J.pseudofunctorOver A : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, which sends `S` to the category of
`A`-valued sheaves on the slice site `C/S` — the over category `Over S` with the localized
topology `J.over S` — and a morphism `g : S' ⟶ S` to the restriction functor
`J.overMapPullback A g`; the canonical glueing datum of a sheaf is the value of
`Pseudofunctor.toDescentData f`, whose object part is the family of restrictions `F|_{C/X i}`
equipped with the coherence isomorphisms of the pseudofunctor. These are the identifications the
source draws as the identity on the left edge of its square, the two restrictions of `F` to an
overlap being restrictions along the two equal composites `C/X i ×_S X j → C/X i → C/S` and
`C/X i ×_S X j → C/X j → C/S`. The conclusion `Functor.IsEquivalence` of that functor is the
source's assertion that the two categories are equivalent *via* it; the equivalence itself, its
quasi-inverse and the unit and counit isomorphisms are then `Functor.asEquivalence`.

Two departures from the source's form, both generalizations, as for Stacks 04TR. First,
`DescentData` records the transition isomorphisms not over chosen fibre products `X i ×_S X j` but
over every object `Y` equipped with morphisms `Y ⟶ X i` and `Y ⟶ X j` agreeing over `S`; the
cocycle condition of the source is `DescentData.hom_comp` and the normalisation `φ i i = id` it
leaves implicit is `DescentData.hom_self`. Writing the overlaps as `U_i ×_U U_j` presupposes that
those fibre products exist, which the definition of a site does not provide; the formulation over
an arbitrary `Y` needs no such assumption, and agrees with the source's whenever they do exist, by
`DescentData'.descentDataEquivalence`. Secondly the sheaves take values in an arbitrary category
`A` rather than in sets, the source's sheaves of sets being the case `A = Type (max u v)`.

The limits in `A` are what the glued sheaf is built from: its sections over `V/S` are cut out of a
limit indexed by the covering sieve at `V`, whose arrows form a type in `Type (max u v)`. The
hypothesis is therefore at size `max u v` and does *not* mention the universe `t` of the index type
`ι`, however large that is.

## References

Stacks Project, tag 04TS (`sites-lemma-mapping-property-glue`); its two halves are tag 04TQ (full
faithfulness) and tag 04TR (essential surjectivity).

* [Stacks 04TS](https://stacks.math.columbia.edu/tag/04TS)
-/


namespace CategoryTheory.GrothendieckTopology

section

universe t v' u' v u w₁ w₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.SheafGluing.DescentEquivalence

section Conjugation

variable {A : Type u'} [Category.{v'} A] {D : Type w₂} [Category.{w₁} D]

/-- A morphism of presheaves is invariant under conjugating by an isomorphism of objects. -/
private lemma app_eq_conj {P Q : Dᵒᵖ ⥤ A} (α : P ⟶ Q) {W₁ W₂ : D} (e : W₁ ≅ W₂)
    {x : P.obj (op W₁) ⟶ P.obj (op W₂)} {y : Q.obj (op W₂) ⟶ Q.obj (op W₁)}
    (hx : x = P.map e.inv.op) (hy : y = Q.map e.hom.op) :
    α.app (op W₁) = x ≫ α.app (op W₂) ≫ y := by
  subst hx hy
  exact (NatTrans.naturality_1 α e.op).symm

end Conjugation

section Prestack

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'} [Category.{v'} A]
  {S : C} (M N : Sheaf (J.over S) A)

/-- The iterated slice functor is natural in the slice: for `q : T' ⟶ T` in `C/S`, an object `V` of
`C/T'.left` lands in `(C/S)/T` in the same way whether it is first viewed over `T'` and then pushed
forward along `q`, or pushed forward to `C/T.left` along `q.left` first. Mathlib has the
corresponding statement for `CategoryTheory.Over.iteratedSliceForward`, where it holds on the nose
(`CategoryTheory.Over.iteratedSliceForwardNaturalityIso`). -/
private def iteratedSliceBackwardMapIso {T T' : Over S} (q : T' ⟶ T) (V : Over T'.left) :
    (Over.map q).obj ((Over.iteratedSliceBackward T').obj V) ≅
      (Over.iteratedSliceBackward T).obj ((Over.map q.left).obj V) :=
  show
    (Over.mk ((Over.homMk V.hom : (Over.mk (V.hom ≫ T'.hom) : Over S) ⟶ T') ≫ q) : Over T) ≅
      Over.mk (Over.homMk (V.hom ≫ q.left) : (Over.mk ((V.hom ≫ q.left) ≫ T.hom) : Over S) ⟶ T)
    from
    Over.isoMk
      (show (Over.mk (V.hom ≫ T'.hom) : Over S) ≅ Over.mk ((V.hom ≫ q.left) ≫ T.hom) from
        Over.isoMk (Iso.refl V.left) (by simp))
      (by
        ext; simp)

/-- Restriction along the iterated slice equivalence `C/T.left ≌ (C/S)/T` identifies the morphisms
of the restrictions of `M` and `N` to `(C/S)/T` with the morphisms of their restrictions to
`C/T.left`. -/
private noncomputable def homEquivIteratedSlice (T : Over S) :
    ((Over.forget T).op ⋙ M.obj ⟶ (Over.forget T).op ⋙ N.obj) ≃
      ((J.overMapPullback A T.hom).obj M ⟶ (J.overMapPullback A T.hom).obj N) :=
  haveI : (Over.iteratedSliceBackward T).IsEquivalence :=
    (Over.iteratedSliceEquiv T).isEquivalence_inverse
  (Functor.FullyFaithful.ofFullyFaithful
        ((Functor.whiskeringLeft (Over T.left)ᵒᵖ (Over T)ᵒᵖ A).obj
          (Over.iteratedSliceBackward T).op)).homEquiv.trans
    (Sheaf.homEquiv (X := (J.overMapPullback A T.hom).obj M) (Y :=
        (J.overMapPullback A T.hom).obj N)).symm

/-- Naturality of `homEquivIteratedSlice`: it commutes with restriction along a morphism
`q : T' ⟶ T` of `C/S`. -/
private lemma homEquivIteratedSlice_naturality {T T' : Over S} (q : T' ⟶ T)
    (α : (Over.forget T).op ⋙ M.obj ⟶ (Over.forget T).op ⋙ N.obj) :
    homEquivIteratedSlice M N T' (Functor.whiskerLeft (Over.map q).op α) =
      ((J.pseudofunctorOver A).presheafHom M N).map q.op (homEquivIteratedSlice M N T α) := by
  obtain ⟨X', a, rfl⟩ := Over.mk_surjective T'
  obtain ⟨u, hu, rfl⟩ : ∃ (u : X' ⟶ T.left) (hu : u ≫ T.hom = a), q = Over.homMk u hu :=
    ⟨q.left, Over.w q, by
      ext; rfl⟩
  subst hu
  ext V : 3
  -- The two objects of `(C/S)/T` at which `α` is evaluated differ by
  -- `iteratedSliceBackwardMapIso`; the identities flanking it are the coherence isomorphisms of
  -- the pseudofunctor, units here.
  let κ := iteratedSliceBackwardMapIso (Over.homMk u : Over.mk (u ≫ T.hom) ⟶ T) V.unop
  exact
    app_eq_conj α κ
      (by
        change 𝟙 _ ≫ ((Over.forget T).op ⋙ M.obj).map κ.inv.op ≫ 𝟙 _ = _; simp)
      (by
        change (𝟙 _ ≫ ((Over.forget T).op ⋙ N.obj).map κ.hom.op) ≫ 𝟙 _ = _; simp)

/-- The presheaf of morphisms of the pseudofunctor of sheaves on the slice sites of `C/S` is the
internal hom presheaf of the site `C/S`. -/
private noncomputable def presheafHomIso :
    presheafHom M.obj N.obj ≅ (J.pseudofunctorOver A).presheafHom M N :=
  NatIso.ofComponents (fun T ↦ (homEquivIteratedSlice M N T.unop).toIso)
    (by
      intro T₁ T₂ p
      ext α
      exact homEquivIteratedSlice_naturality M N p.unop α)

end Prestack

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A]

/-- **Maps of sheaves glue** (Stacks 04TQ): the pseudofunctor of sheaves on the slice sites is a
prestack. -/
private lemma isPrestack : (J.pseudofunctorOver A).IsPrestack J :=
  ⟨fun M N ↦ (Presheaf.isSheaf_of_iso_iff (presheafHomIso M N)).1 (N.property.hom M.obj)⟩

/-- The pseudofunctor of sheaves on the slice sites is a stack. -/
private lemma isStack [HasLimitsOfSize.{max u v, max u v} A] : (J.pseudofunctorOver A).IsStack J
    where
  toIsPrestack := isPrestack J A
  essSurj_of_sieve R hR :=
    GrothendieckTopology.essSurj_toDescentData_pseudofunctorOver J A
      (fun g : R.arrows.category ↦ g.obj.hom) (by rwa [Sieve.ofArrows_category])

end

end Stacks.SheafGluing.DescentEquivalence

@[expose] public section

open Stacks.SheafGluing.DescentEquivalence in
/-- **Sheaves on a slice site are glueing data.** Let `(C, J)` be a site, let `{f i : X i ⟶ S}` be
a covering of an object `S` of `C`, and let `A` be a category with limits of the relevant size.
Then the category of `A`-valued sheaves on the slice site `C/S` is equivalent to the category of
glueing data for `A`-valued sheaves with respect to `{f i : X i ⟶ S}` — a sheaf `F i` on each
slice site `C/X i` together with isomorphisms between the restrictions of `F i` and of `F j` over
the overlaps, satisfying the cocycle condition over the triple overlaps — via the functor sending
a sheaf `F` on `C/S` to its canonical glueing datum `(F|_{C/X i})`. -/
@[stacks 04TS]
public theorem isEquivalence_toDescentData_pseudofunctorOver {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A]
    [HasLimitsOfSize.{max u v, max u v} A] {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hf : Sieve.ofArrows X f ∈ J S) : ((J.pseudofunctorOver A).toDescentData f).IsEquivalence :=
  have := isStack J A
  Pseudofunctor.isEquivalence_toDescentData _ f hf

end

end

end CategoryTheory.GrothendieckTopology
