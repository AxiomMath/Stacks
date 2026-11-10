module

public import StacksFrontier.Topology.Sheaves.Limits.PullbackSections
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Topology.Sheaves.Forget

/-!
# The abelian germ model for the pullback of a sheaf of abelian groups

`StacksFrontier.Topology.Sheaves.Limits.GermPullback` realises the pullback `g⁻¹𝒢` of a presheaf of
**types** along a continuous map `g : Z → Y` as a sheaf of germs: a section over `W ⊆ Z` is a
function `W → Σ y, 𝒢.stalk y` which is locally the family of germs of a single section of `𝒢`.
That model is what makes the slice diagram of Stacks 0A32 an honest functor, pullback along a
further map being literally precomposition.  It is also irreducibly `Type`-valued: it is
`TopCat.subsheafToTypes` of a `PrelocalPredicate`, and there is no abelian `subsheafToTypes`.

This file supplies the missing abelian structure.  For `𝒢` a presheaf of abelian groups it puts
an `AddCommGroup` on every stalk of the underlying presheaf of types `typePresheaf 𝒢`, and then
an `AddCommGroup` on the germ-model sections `(sheaf g (typePresheaf 𝒢))(W)` by **pointwise
addition of germs** — the point being that the defining local condition of the model *is* closed
under it.  With that, the set-level Stacks 0A32 becomes a statement about a colimit of abelian
groups.

## Main definitions

* `GermPullback.typePresheaf`: the underlying presheaf of types, `𝒢 ⋙ forget AddCommGrpCat`.
* `GermPullback.stalkAddCommGroup`, `GermPullback.stalkAddEquiv`: the abelian group structure on
  `(typePresheaf 𝒢).stalkOfSize y`, transported along the canonical bijection with `𝒢.stalk y`.
  The stalk is a filtered colimit and `forget AddCommGrpCat` preserves filtered colimits, which is
  where that bijection comes from.
* `GermPullback.germValue`: the value of a germ `a : Σ y, (typePresheaf 𝒢).stalkOfSize y` *in the
  stalk at a prescribed point* `y`: the second component of `a` when `a` is based at `y`, and `0`
  otherwise.  This is what keeps the group operations free of dependent casts.
* `GermPullback.FibrePred`, `GermPullback.predSubgroup`, `GermPullback.sectionsEquiv`: the local
  condition of the germ model read on a *fibrewise* family
  `f z ∈ (typePresheaf 𝒢).stalkOfSize (g z)`, the subgroup of families satisfying it, and its
  bijection with the germ-model sections.
* `GermPullback.instAddCommGroupSections`: the abelian group of germ-model sections over `W`.
* `GermPullback.comapAddHom`, `GermPullback.ofSectionAddHom`: pullback of sections along a
  further map, and the germwise pullback of a section of `𝒢`, as morphisms of abelian groups.
* `GermPullback.abelianPresheaf`, `GermPullback.abelianSheaf`: **the abelian germ model** — the
  germ model itself, lifted to a sheaf of *abelian groups*, which is possible because restriction
  is additive.  Composing with `forget AddCommGrpCat` returns the `Type`-valued germ model on the
  nose (`GermPullback.abelianSheaf_presheaf_comp_forget`), so everything already proved about the
  latter applies to it verbatim.
* `GermPullback.typeSheaf`: the underlying sheaf of types of a sheaf of abelian groups.

The abelian form of Stacks 0A32 itself — `SpectralDiagram.abelianSliceFunctor`,
`SpectralDiagram.abelianSliceCocone` and `SpectralDiagram.isColimitAbelianSliceCocone` — is built
on top of this in `StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian`, which is where the
transport principle along `forget AddCommGrpCat` lives.

## Main results

* `GermPullback.fibrePred_add`, `GermPullback.fibrePred_zero`, `GermPullback.fibrePred_neg`:
  **the local condition of the germ model is closed under pointwise addition**, and contains the
  zero family and pointwise negations.  This is the one step that could have failed, and it does
  not: if `f₁` is germwise `s₁ ∈ 𝒢(V₁)` near `z` and `f₂` is germwise `s₂ ∈ 𝒢(V₂)` near `z`, then
  `f₁ + f₂` is germwise `s₁|_{V₁ ⊓ V₂} + s₂|_{V₁ ⊓ V₂} ∈ 𝒢(V₁ ⊓ V₂)` there, because the germ
  maps of `𝒢` are additive (`GermPullback.germ_resAdd`).
* `GermPullback.add_of_germ_spec`: **a map between stalks of underlying type presheaves which is
  prescribed on germs by an additive family of maps on sections is additive.**  This is the tool
  for the maps of the germ model that are *not* precomposition — the stalk map of an `f`-map,
  which is what the transition maps of the pullback system of Stacks 0A33 are built from.  Two
  germs at a point are germs of sections over one common open, and there the germ map is additive.
* `GermPullback.germValue_add_mk`, `GermPullback.germValue_zero_mk`: reading a sum of germs based
  at one point in a prescribed stalk is additive, in both cases of `germValue`.
* `GermPullback.comap_add`, `GermPullback.presheafMap_add`, `GermPullback.ofSection_add`:
  pullback along a further map, restriction along an inclusion of opens, and the germwise
  pullback of a section
  of `𝒢` are all additive.  Pullback and restriction are precomposition, so this is immediate
  from the pointwise description of the sum.
* `GermPullback.typeSheaf_presheaf`: the underlying presheaf of `typeSheaf ℱ` is
  `typePresheaf ℱ.presheaf`, by definition.  This is what lets Stacks 0A32 for sheaves
  of sets be applied to a sheaf of abelian groups with the group structures of this file on both
  sides of its canonical map.

## Implementation notes

The group structure on `(typePresheaf 𝒢).stalkOfSize y` is *transported* from `𝒢.stalk y`, not
built by
hand.  Everything downstream uses it only through `germ_add`, `germ_zero` and `germ_neg` — the
additivity of the germ maps — proved from `ι_preservesColimitIso_hom`, i.e. from the
compatibility of the transporting bijection with the colimit injections.

The group structure on the sections is likewise transported, from `predSubgroup`.  A germ-model
section over `W` is a function `W → Σ y, (typePresheaf 𝒢).stalkOfSize y`, and a `Σ`-type carries no
addition; but the first component at `z` is forced to be `g z` (`GermPullback.fst_apply`), so
such a section is the same thing as a fibrewise family `f z ∈ (typePresheaf 𝒢).stalkOfSize (g z)`
subject to the same local condition.  Those form an honest `AddSubgroup` of a product of abelian
groups, where addition is pointwise with no dependent cast anywhere; `sectionsEquiv` carries that
structure back.  The bridge in the other direction is `germValue`, which is deliberately total,
with `0` as its value at a point other than the base point of the germ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

noncomputable section

namespace GermPullback

variable {Y Z Z' : TopCat.{u}}

/-! ### The underlying presheaf of types, and the abelian structure on its stalks -/

/-- The underlying presheaf of types of a presheaf of abelian groups. -/
abbrev typePresheaf (𝒢 : Y.Presheaf AddCommGrpCat.{u}) : Y.Presheaf (Type u) :=
  𝒢 ⋙ forget AddCommGrpCat.{u}

variable (𝒢 : Y.Presheaf AddCommGrpCat.{u})

/-- The diagram of open neighbourhoods of `y` whose colimit is the stalk of `𝒢` at `y`. -/
abbrev nhdsDiagram (y : Y) : (OpenNhds y)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OpenNhds.inclusion y).op ⋙ 𝒢

/-- The canonical comparison isomorphism `𝒢.stalk y ≅ (typePresheaf 𝒢).stalkOfSize y` of types: the
stalk is a filtered colimit and `forget AddCommGrpCat` preserves filtered colimits. -/
def stalkIso (y : Y) :
    (forget AddCommGrpCat.{u}).obj (𝒢.stalk y) ≅ (typePresheaf 𝒢).stalkOfSize y :=
  preservesColimitIso (forget AddCommGrpCat.{u}) (nhdsDiagram 𝒢 y)

/-- The canonical bijection from the stalk of the underlying presheaf of types to the underlying
type of the stalk of `𝒢`. -/
def stalkEquiv (y : Y) :
    (typePresheaf 𝒢).stalkOfSize y ≃ (forget AddCommGrpCat.{u}).obj (𝒢.stalk y) :=
  (stalkIso 𝒢 y).toEquiv.symm

/-- **The abelian group structure on a stalk of the underlying presheaf of types**, transported
along `stalkEquiv` from the stalk of `𝒢` itself. -/
instance stalkAddCommGroup (y : Y) : AddCommGroup ((typePresheaf 𝒢).stalkOfSize y) :=
  Equiv.addCommGroup (stalkEquiv 𝒢 y)

/-- `stalkEquiv` is additive for the transported structure, by construction. -/
def stalkAddEquiv (y : Y) :
    (typePresheaf 𝒢).stalkOfSize y ≃+ (forget AddCommGrpCat.{u}).obj (𝒢.stalk y) where
  __ := stalkEquiv 𝒢 y
  map_add' a b := by
    change stalkEquiv 𝒢 y ((stalkEquiv 𝒢 y).symm _) = _
    rw [Equiv.apply_symm_apply]

/-- The transporting bijection carries the germ map of `𝒢` to the germ map of its underlying
presheaf of types: both are the colimit injection at the open neighbourhood `V`. -/
lemma stalkEquiv_symm_germ (y : Y) (V : Opens Y) (hy : y ∈ V) (s : 𝒢.obj (op V)) :
    (stalkEquiv 𝒢 y).symm (𝒢.germ V y hy s) = (typePresheaf 𝒢).germOfSize V y hy s := by
  change (stalkIso 𝒢 y).hom _ = _
  exact congrFun (congrArg (fun f ↦ (ConcreteCategory.hom f : _ → _))
    (ι_preservesColimitIso_hom (forget AddCommGrpCat.{u}) (nhdsDiagram 𝒢 y) (op ⟨V, hy⟩))) s

/-- The germ map of the underlying presheaf of types, as a morphism of abelian groups. -/
def germAddHom (V : Opens Y) {y : Y} (hy : y ∈ V) :
    𝒢.obj (op V) →+ (typePresheaf 𝒢).stalkOfSize y :=
  ((stalkAddEquiv 𝒢 y).symm.toAddMonoidHom).comp (ConcreteCategory.hom (𝒢.germ V y hy))

/-- `germAddHom` is the germ map. -/
@[simp]
lemma germAddHom_apply (V : Opens Y) {y : Y} (hy : y ∈ V) (s : 𝒢.obj (op V)) :
    germAddHom 𝒢 V hy s = (typePresheaf 𝒢).germOfSize V y hy s :=
  stalkEquiv_symm_germ 𝒢 y V hy s

/-- **The germ maps of `typePresheaf 𝒢` are additive.** -/
lemma germ_add (V : Opens Y) {y : Y} (hy : y ∈ V) (s t : 𝒢.obj (op V)) :
    (typePresheaf 𝒢).germOfSize V y hy (s + t) =
      (typePresheaf 𝒢).germOfSize V y hy s + (typePresheaf 𝒢).germOfSize V y hy t := by
  rw [← germAddHom_apply 𝒢 V hy, ← germAddHom_apply 𝒢 V hy, ← germAddHom_apply 𝒢 V hy, map_add]

/-- The germ of the zero section is zero. -/
lemma germ_zero (V : Opens Y) {y : Y} (hy : y ∈ V) :
    (typePresheaf 𝒢).germOfSize V y hy (0 : 𝒢.obj (op V)) = 0 := by
  rw [← germAddHom_apply 𝒢 V hy, map_zero]

/-- The germ maps commute with negation. -/
lemma germ_neg (V : Opens Y) {y : Y} (hy : y ∈ V) (s : 𝒢.obj (op V)) :
    (typePresheaf 𝒢).germOfSize V y hy (-s) = -(typePresheaf 𝒢).germOfSize V y hy s := by
  rw [← germAddHom_apply 𝒢 V hy, ← germAddHom_apply 𝒢 V hy, map_neg]

/-- The sum, over the intersection of their domains, of a section of `𝒢` on `V₁` and a section of
`𝒢` on `V₂`.  This is the witness that makes the local condition of the germ model closed under
pointwise addition. -/
def resAdd {V₁ V₂ : Opens Y} (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) :
    𝒢.obj (op (V₁ ⊓ V₂)) :=
  ConcreteCategory.hom (𝒢.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op) s₁ +
    ConcreteCategory.hom (𝒢.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op) s₂

/-- The germ of `resAdd s₁ s₂` at a common point of `V₁` and `V₂` is the sum of the germ of `s₁`
and the germ of `s₂` there. -/
lemma germ_resAdd {V₁ V₂ : Opens Y} (s₁ : 𝒢.obj (op V₁)) (s₂ : 𝒢.obj (op V₂)) {y : Y}
    (h₁ : y ∈ V₁) (h₂ : y ∈ V₂) :
    (typePresheaf 𝒢).germOfSize (V₁ ⊓ V₂) y ⟨h₁, h₂⟩ (resAdd 𝒢 s₁ s₂) =
      (typePresheaf 𝒢).germOfSize V₁ y h₁ s₁ + (typePresheaf 𝒢).germOfSize V₂ y h₂ s₂ := by
  rw [resAdd, germ_add 𝒢 (V₁ ⊓ V₂) (⟨h₁, h₂⟩ : y ∈ V₁ ⊓ V₂)]
  exact congrArg₂ (· + ·) ((typePresheaf 𝒢).germOfSize_res_apply (homOfLE inf_le_left) y _ s₁)
    ((typePresheaf 𝒢).germOfSize_res_apply (homOfLE inf_le_right) y _ s₂)

/-- **A map of stalks prescribed on germs by an additive family is additive.**  Let `ψ` be a map
from the stalk of `typePresheaf 𝒢` at `y` to the stalk of `typePresheaf ℋ` at `z`, and suppose
that for every open `V ∋ y` it carries the germ at `y` of a section `s ∈ 𝒢(V)` to the germ at `z`
of `ν V s ∈ ℋ(Φ V)`, each `ν V` being additive.  Then `ψ` is additive.

Two germs at `y` are germs of two sections over a common open `V₁ ⊓ V₂` — this is
`TopCat.Presheaf.germ_res_apply` — and there the germ map is additive (`germ_add`), so both sides
are computed from a single application of `ν (V₁ ⊓ V₂)`.  Neither monotonicity of `Φ` nor any
compatibility of `ν` with restriction is needed. -/
lemma add_of_germ_spec {ℋ : Z.Presheaf AddCommGrpCat.{u}} {y : Y} {z : Z}
    (Φ : Opens Y → Opens Z) (ν : ∀ V : Opens Y, 𝒢.obj (op V) → ℋ.obj (op (Φ V)))
    (ψ : (typePresheaf 𝒢).stalkOfSize y → (typePresheaf ℋ).stalkOfSize z)
    (hmem : ∀ V : Opens Y, y ∈ V → z ∈ Φ V)
    (hψ : ∀ (V : Opens Y) (hV : y ∈ V) (s : 𝒢.obj (op V)),
      ψ ((typePresheaf 𝒢).germOfSize V y hV s) =
        (typePresheaf ℋ).germOfSize (Φ V) z (hmem V hV) (ν V s))
    (hν : ∀ (V : Opens Y) (s t : 𝒢.obj (op V)), ν V (s + t) = ν V s + ν V t)
    (ξ ζ : (typePresheaf 𝒢).stalkOfSize y) :
    ψ (ξ + ζ) = ψ ξ + ψ ζ := by
  obtain ⟨V₁, h₁, s₁, hs₁⟩ := (typePresheaf 𝒢).exists_germOfSize_eq ξ
  obtain ⟨V₂, h₂, s₂, hs₂⟩ := (typePresheaf 𝒢).exists_germOfSize_eq ζ
  have hV : y ∈ V₁ ⊓ V₂ := ⟨h₁, h₂⟩
  have e₁ := ((typePresheaf 𝒢).germOfSize_res_apply
    (homOfLE (inf_le_left (a := V₁) (b := V₂))) y hV s₁).trans hs₁
  have e₂ := ((typePresheaf 𝒢).germOfSize_res_apply
    (homOfLE (inf_le_right (a := V₁) (b := V₂))) y hV s₂).trans hs₂
  rw [← e₁, ← e₂, ← germ_add 𝒢 (V₁ ⊓ V₂) hV, hψ _ hV, hψ _ hV, hψ _ hV, hν,
    germ_add ℋ (Φ (V₁ ⊓ V₂)) (hmem _ hV)]

/-! ### The value of a germ in a prescribed stalk -/

open Classical in
/-- The value of a germ `a` in the stalk at `y`: the second component of `a` when `a` is based at
`y`, and `0` otherwise.  Germ-model sections are based at `g z` at the point `z`
(`fst_apply`), so this reads off their stalk value with no dependent cast. -/
def germValue (a : Germs.{u, u} (typePresheaf 𝒢)) (y : Y) : (typePresheaf 𝒢).stalkOfSize y :=
  if h : a.1 = y then h ▸ a.2 else 0

/-- The value of a germ in the stalk at its own base point is its second component. -/
lemma germValue_self (a : Germs.{u, u} (typePresheaf 𝒢)) : germValue 𝒢 a a.1 = a.2 :=
  dite_eq_left_of_eq_true (eq_true rfl)

/-- The value at `y` of the germ `⟨y, s⟩` is `s`. -/
@[simp]
lemma germValue_mk {y : Y} (s : (typePresheaf 𝒢).stalkOfSize y) :
    germValue 𝒢 (⟨y, s⟩ : Germs.{u, u} (typePresheaf 𝒢)) y = s :=
  dite_eq_left_of_eq_true (eq_true rfl)

/-- A germ based at `y` is recovered from its value in the stalk at `y`. -/
lemma mk_germValue {a : Germs.{u, u} (typePresheaf 𝒢)} {y : Y} (h : a.1 = y) :
    (⟨y, germValue 𝒢 a y⟩ : Germs.{u, u} (typePresheaf 𝒢)) = a := by
  subst h
  exact congrArg (Sigma.mk a.1) (germValue_self 𝒢 a)

/-- Two germs based at the same point are equal exactly when their stalk components are. -/
lemma snd_eq_of_mk_eq {y : Y} {a b : (typePresheaf 𝒢).stalkOfSize y}
    (h : (⟨y, a⟩ : Germs.{u, u} (typePresheaf 𝒢)) = ⟨y, b⟩) : a = b :=
  ((germValue_mk 𝒢 a).symm.trans (congrArg (fun c ↦ germValue 𝒢 c y) h)).trans (germValue_mk 𝒢 b)

/-- **The value in a prescribed stalk of a sum of germs based at one point.**  The two cases of
`germValue` are both additive: at the base point it reads off the second component, elsewhere it
is zero. -/
lemma germValue_add_mk {y₀ : Y} (ξ ζ : (typePresheaf 𝒢).stalkOfSize y₀) (y : Y) :
    germValue 𝒢 ⟨y₀, ξ + ζ⟩ y =
      germValue 𝒢 (⟨y₀, ξ⟩ : Germs.{u, u} (typePresheaf 𝒢)) y +
        germValue 𝒢 (⟨y₀, ζ⟩ : Germs.{u, u} (typePresheaf 𝒢)) y := by
  by_cases h : y₀ = y
  · subst h; rw [germValue_mk, germValue_mk, germValue_mk]
  · simp only [germValue, h, dite_false, add_zero]

/-- The value of a zero germ in any stalk is zero. -/
lemma germValue_zero_mk {y₀ : Y} (y : Y) :
    germValue 𝒢 (⟨y₀, (0 : (typePresheaf 𝒢).stalkOfSize y₀)⟩ :
      Germs.{u, u} (typePresheaf 𝒢)) y = 0 := by
  by_cases h : y₀ = y
  · subst h; rw [germValue_mk]
  · simp only [germValue, h, dite_false]

/-- Moving the base point of a germ built from the sum of two germ values. -/
lemma mk_germValue_add (a b : Germs.{u, u} (typePresheaf 𝒢)) {y y' : Y} (e : y = y') :
    (⟨y, germValue 𝒢 a y + germValue 𝒢 b y⟩ : Germs.{u, u} (typePresheaf 𝒢)) =
      ⟨y', germValue 𝒢 a y' + germValue 𝒢 b y'⟩ := by
  subst e; rfl

/-- Moving the base point of the zero germ. -/
lemma mk_zero_congr {y y' : Y} (e : y = y') :
    (⟨y, (0 : (typePresheaf 𝒢).stalkOfSize y)⟩ : Germs.{u, u} (typePresheaf 𝒢)) = ⟨y', 0⟩ := by
  subst e; rfl

/-! ### The local condition read fibrewise -/

variable {g : Z → Y}

/-- **The germ of a germ-model section at `z` is based at `g z`.**  Locally the section is the
family of germs of a section of `𝒢`, whose value at `z` is by construction based at `g z`. -/
lemma fst_apply {W : Opens Z} (σ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    (σ.1 z).1 = g z.1 := by
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := σ.2 z
  have h : σ.1 (i ⟨z.1, hz₀⟩) =
      ⟨g z.1, (typePresheaf 𝒢).germOfSize V (g z.1) (hV ⟨z.1, hz₀⟩) s⟩ := hs ⟨z.1, hz₀⟩
  have hiz : i ⟨z.1, hz₀⟩ = z := Subtype.ext rfl
  have h2 := congrArg Sigma.fst h
  rw [hiz] at h2
  exact h2

/-- The stalk value of a germ-model section at a point of its domain: an element of the stalk of
`typePresheaf 𝒢` at the image point. -/
def stalkVal {W : Opens Z} (σ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    (typePresheaf 𝒢).stalkOfSize (g z.1) :=
  germValue 𝒢 (σ.1 z) (g z.1)

/-- A germ-model section is recovered from its stalk values. -/
lemma val_eq_mk {W : Opens Z} (σ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    (⟨g z.1, stalkVal 𝒢 σ z⟩ : Germs.{u, u} (typePresheaf 𝒢)) = σ.1 z :=
  mk_germValue 𝒢 (fst_apply 𝒢 σ z)

/-- The local condition of the germ model, read on a fibrewise family: `f` is *locally germwise*
if the germ-valued function `z ↦ ⟨g z, f z⟩` satisfies the sheafified predicate `pre g 𝒢`. -/
def FibrePred (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) {W : Opens Z}
    (f : ∀ z : W, (typePresheaf 𝒢).stalkOfSize (g z.1)) : Prop :=
  (pre g (typePresheaf 𝒢)).sheafify.pred fun z ↦ ⟨g z.1, f z⟩

/-- **The local condition of the germ model is closed under pointwise addition.**  Near `z` the
family `f₁` is germwise `s₁ ∈ 𝒢(V₁)` and `f₂` is germwise `s₂ ∈ 𝒢(V₂)`; on the intersection of
the two neighbourhoods `f₁ + f₂` is then germwise `resAdd s₁ s₂ ∈ 𝒢(V₁ ⊓ V₂)`, because the germ
maps of `𝒢` are additive. -/
lemma fibrePred_add {W : Opens Z} {f₁ f₂ : ∀ z : W, (typePresheaf 𝒢).stalkOfSize (g z.1)}
    (h₁ : FibrePred g 𝒢 f₁) (h₂ : FibrePred g 𝒢 f₂) :
    FibrePred g 𝒢 (f₁ + f₂) := by
  intro z
  obtain ⟨W₁, hz₁, i₁, V₁, hV₁, s₁, hs₁⟩ := h₁ z
  obtain ⟨W₂, hz₂, i₂, V₂, hV₂, s₂, hs₂⟩ := h₂ z
  refine ⟨W₁ ⊓ W₂, ⟨hz₁, hz₂⟩, homOfLE inf_le_left ≫ i₁, V₁ ⊓ V₂,
    fun x ↦ ⟨hV₁ ⟨x.1, x.2.1⟩, hV₂ ⟨x.1, x.2.2⟩⟩, resAdd 𝒢 s₁ s₂, fun x ↦ ?_⟩
  change (⟨g x.1, f₁ (i₁ ⟨x.1, x.2.1⟩) + f₂ (i₂ ⟨x.1, x.2.2⟩)⟩ :
    Germs.{u, u} (typePresheaf 𝒢)) = _
  rw [snd_eq_of_mk_eq 𝒢 (hs₁ ⟨x.1, x.2.1⟩), snd_eq_of_mk_eq 𝒢 (hs₂ ⟨x.1, x.2.2⟩),
    germ_resAdd 𝒢 s₁ s₂ (hV₁ ⟨x.1, x.2.1⟩) (hV₂ ⟨x.1, x.2.2⟩)]

/-- The zero family satisfies the local condition: it is germwise the zero section of `𝒢` on all
of `Y`. -/
lemma fibrePred_zero {W : Opens Z} :
    FibrePred g 𝒢 (0 : ∀ z : W, (typePresheaf 𝒢).stalkOfSize (g z.1)) := by
  intro z
  refine ⟨W, z.2, 𝟙 W, ⊤, fun _ ↦ trivial, (0 : 𝒢.obj (op (⊤ : Opens Y))), fun x ↦ ?_⟩
  change (⟨g x.1, (0 : (typePresheaf 𝒢).stalkOfSize (g x.1))⟩ : Germs.{u, u} (typePresheaf 𝒢)) = _
  refine congrArg (Sigma.mk (g x.1)) ?_
  exact (germ_zero 𝒢 ⊤ (trivial : g x.1 ∈ (⊤ : Opens Y))).symm

/-- The local condition is closed under pointwise negation. -/
lemma fibrePred_neg {W : Opens Z} {f : ∀ z : W, (typePresheaf 𝒢).stalkOfSize (g z.1)}
    (h : FibrePred g 𝒢 f) : FibrePred g 𝒢 (-f) := by
  intro z
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := h z
  refine ⟨W₀, hz₀, i, V, hV, -s, fun x ↦ ?_⟩
  change (⟨g x.1, -f (i x)⟩ : Germs.{u, u} (typePresheaf 𝒢)) = _
  rw [snd_eq_of_mk_eq 𝒢 (hs x)]
  exact congrArg (Sigma.mk (g x.1)) (germ_neg 𝒢 V (hV x) s).symm

/-- The abelian group of locally-germwise fibrewise families over `W`, as a subgroup of the
product of the stalks. -/
def predSubgroup (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) (W : Opens Z) :
    AddSubgroup (∀ z : W, (typePresheaf 𝒢).stalkOfSize (g z.1)) where
  carrier := {f | FibrePred g 𝒢 f}
  add_mem' h₁ h₂ := fibrePred_add 𝒢 h₁ h₂
  zero_mem' := fibrePred_zero 𝒢
  neg_mem' h := fibrePred_neg 𝒢 h

/-- **Germ-model sections are the locally-germwise fibrewise families.**  In one direction take
stalk values, in the other build the germ based at `g z`; the two are inverse because the germ of
a section at `z` is based at `g z`. -/
def sectionsEquiv (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) (W : Opens Z) :
    (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W) ≃ predSubgroup g 𝒢 W where
  toFun σ := ⟨stalkVal 𝒢 σ, by
    change (pre g (typePresheaf 𝒢)).sheafify.pred fun z ↦ ⟨g z.1, stalkVal 𝒢 σ z⟩
    rw [funext fun z ↦ val_eq_mk 𝒢 σ z]
    exact σ.2⟩
  invFun f := ⟨fun z ↦ ⟨g z.1, f.1 z⟩, f.2⟩
  left_inv σ := Subtype.ext (funext fun z ↦ val_eq_mk 𝒢 σ z)
  right_inv f := Subtype.ext (funext fun z ↦ germValue_mk 𝒢 (f.1 z))

/-- **The abelian group of germ-model sections over `W`**, transported from `predSubgroup`:
addition, zero and negation are computed on stalk values at each point, and `fibrePred_add`,
`fibrePred_zero`, `fibrePred_neg` say the defining local condition survives them. -/
instance instAddCommGroupSections {W : Opens Z} :
    AddCommGroup ((sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) :=
  Equiv.addCommGroup (sectionsEquiv g 𝒢 W)

/-- The sum of two germ-model sections takes at `z` the germ based at `g z` whose stalk value is
the sum of the two stalk values. -/
@[simp]
lemma add_val {W : Opens Z} (σ τ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    (σ + τ).1 z = ⟨g z.1, stalkVal 𝒢 σ z + stalkVal 𝒢 τ z⟩ := rfl

/-- The stalk value of a sum is the sum of the stalk values. -/
@[simp]
lemma stalkVal_add {W : Opens Z} (σ τ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    stalkVal 𝒢 (σ + τ) z = stalkVal 𝒢 σ z + stalkVal 𝒢 τ z :=
  germValue_mk 𝒢 _

/-- The zero germ-model section takes at `z` the zero germ based at `g z`. -/
@[simp]
lemma zero_val {W : Opens Z} (z : W) :
    (0 : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)).1 z = ⟨g z.1, 0⟩ := rfl

/-- The stalk value of the zero section is zero. -/
@[simp]
lemma stalkVal_zero {W : Opens Z} (z : W) :
    stalkVal 𝒢 (0 : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) z = 0 :=
  germValue_mk 𝒢 _

/-- The negation of a germ-model section is computed on stalk values. -/
@[simp]
lemma neg_val {W : Opens Z} (σ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    (-σ).1 z = ⟨g z.1, -stalkVal 𝒢 σ z⟩ := rfl

/-- The stalk value of a negation is the negation of the stalk value. -/
@[simp]
lemma stalkVal_neg {W : Opens Z} (σ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) (z : W) :
    stalkVal 𝒢 (-σ) z = -stalkVal 𝒢 σ z :=
  germValue_mk 𝒢 _

/-- The stalk value of a germwise-generated section is the germ of the generating section. -/
@[simp]
lemma stalkVal_ofSection {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V)
    (s : 𝒢.obj (op V)) (z : W) :
    stalkVal 𝒢 (ofSection (𝒢 := typePresheaf 𝒢) hV s) z =
      (typePresheaf 𝒢).germOfSize V (g z.1) (hV z) s :=
  germValue_mk 𝒢 _

/-! ### Additivity of restriction, pullback and the germwise pullback -/

/-- **Restriction along an inclusion of opens is additive**: restriction is precomposition, and
the sum is computed pointwise. -/
lemma presheafMap_add {W W' : Opens Z} (i : W' ⟶ W)
    (σ τ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) :
    (sheaf g (typePresheaf 𝒢)).presheaf.map i.op (σ + τ) =
      (sheaf g (typePresheaf 𝒢)).presheaf.map i.op σ +
        (sheaf g (typePresheaf 𝒢)).presheaf.map i.op τ :=
  rfl

/-- Restriction along an inclusion of opens sends zero to zero. -/
lemma presheafMap_zero {W W' : Opens Z} (i : W' ⟶ W) :
    (sheaf g (typePresheaf 𝒢)).presheaf.map i.op
      (0 : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) = 0 :=
  rfl

/-- The germwise pullback of a section of `𝒢` is additive in that section. -/
lemma ofSection_add {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V)
    (s t : 𝒢.obj (op V)) :
    ofSection (g := g) (𝒢 := typePresheaf 𝒢) hV (s + t) =
      ofSection (𝒢 := typePresheaf 𝒢) hV s + ofSection (𝒢 := typePresheaf 𝒢) hV t := by
  refine ext fun z ↦ ?_
  rw [ofSection_val, add_val, stalkVal_ofSection, stalkVal_ofSection]
  exact congrArg (Sigma.mk (g z.1)) (germ_add 𝒢 V (hV z) s t)

/-- The germwise pullback of a section of `𝒢`, as a morphism of abelian groups. -/
def ofSectionAddHom {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V) :
    𝒢.obj (op V) →+ (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W) where
  toFun s := ofSection (𝒢 := typePresheaf 𝒢) hV s
  map_zero' := by
    refine ext fun z ↦ ?_
    rw [ofSection_val, zero_val]
    exact congrArg (Sigma.mk (g z.1)) (germ_zero 𝒢 V (hV z))
  map_add' := ofSection_add 𝒢 hV

variable {g' : Z' → Y} {h : Z' → Z}

/-- **Pullback of sections along a further map is additive**: it is precomposition. -/
lemma comap_add (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'}
    (hW : ∀ z : W', h z.1 ∈ W) (σ τ : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) :
    comap hh hcomp hW (σ + τ) = comap hh hcomp hW σ + comap hh hcomp hW τ :=
  ext fun z ↦
    (mk_germValue_add 𝒢 (σ.1 ⟨h z.1, hW z⟩) (τ.1 ⟨h z.1, hW z⟩) (hcomp z.1)).symm

/-- Pullback of sections along a further map sends zero to zero. -/
lemma comap_zero (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'}
    (hW : ∀ z : W', h z.1 ∈ W) :
    comap hh hcomp hW (0 : (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) = 0 :=
  ext fun z ↦ (mk_zero_congr 𝒢 (hcomp z.1)).symm

/-- Pullback of sections along a further map, as a morphism of abelian groups. -/
def comapAddHom (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'}
    (hW : ∀ z : W', h z.1 ∈ W) :
    (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W) →+
      (sheaf g' (typePresheaf 𝒢)).presheaf.obj (op W') where
  toFun := comap hh hcomp hW
  map_zero' := comap_zero 𝒢 hh hcomp hW
  map_add' := comap_add 𝒢 hh hcomp hW

/-! ### The germ model as a sheaf of abelian groups -/

/-- Restriction along an inclusion of opens, as a morphism of abelian groups. -/
def presheafMapAddHom {W W' : Opens Z} (i : W' ⟶ W) :
    (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W) →+
      (sheaf g (typePresheaf 𝒢)).presheaf.obj (op W') where
  toFun := (sheaf g (typePresheaf 𝒢)).presheaf.map i.op
  map_zero' := presheafMap_zero 𝒢 i
  map_add' := presheafMap_add 𝒢 i

/-- **The germ model as a presheaf of abelian groups.**  The sections over `W` carry the group
structure of `instAddCommGroupSections` and restriction is additive, so the `Type`-valued germ
model lifts to `AddCommGrpCat` with no change to the underlying data: composing with
`forget AddCommGrpCat` gives back `(sheaf g (typePresheaf 𝒢)).presheaf`. -/
def abelianPresheaf (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) :
    Z.Presheaf AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of ((sheaf g (typePresheaf 𝒢)).presheaf.obj (op W.unop))
  map {_ _} i := AddCommGrpCat.ofHom (presheafMapAddHom 𝒢 i.unop)
  map_id _ := ConcreteCategory.hom_ext _ _ fun _ ↦ ext fun _ ↦ rfl
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun _ ↦ ext fun _ ↦ rfl

/-- The underlying presheaf of types of `abelianPresheaf` is the germ model itself. -/
lemma abelianPresheaf_comp_forget (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) :
    typePresheaf (abelianPresheaf g 𝒢) = (sheaf g (typePresheaf 𝒢)).presheaf := rfl

/-- **The abelian germ model: the pullback `g⁻¹𝒢` of a presheaf of abelian groups, as a sheaf of
abelian groups.**  Its underlying sheaf of types is the germ model `GermPullback.sheaf`, so every
statement already proved about that model — in particular Stacks 0A32 — applies to it verbatim,
now with group structures on both sides.  The sheaf condition is the one of the germ model,
transported back by `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`. -/
def abelianSheaf (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) : Z.Sheaf AddCommGrpCat.{u} :=
  ⟨abelianPresheaf g 𝒢,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u})
      (abelianPresheaf g 𝒢)).2 (sheaf g (typePresheaf 𝒢)).2⟩

/-- The underlying sheaf of types of the abelian germ model is the germ model. -/
lemma abelianSheaf_presheaf_comp_forget (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) :
    typePresheaf (abelianSheaf g 𝒢).presheaf = (sheaf g (typePresheaf 𝒢)).presheaf := rfl

/-- Sections of the abelian germ model over `W` are the germ-model sections over `W`, with the
group structure of `instAddCommGroupSections`. -/
lemma abelianSheaf_obj (g : Z → Y) (𝒢 : Y.Presheaf AddCommGrpCat.{u}) (W : Opens Z) :
    (abelianSheaf g 𝒢).presheaf.obj (op W) =
      AddCommGrpCat.of ((sheaf g (typePresheaf 𝒢)).presheaf.obj (op W)) := rfl

/-! ### The underlying sheaf of types of a sheaf of abelian groups -/

/-- The underlying sheaf of types of a sheaf of abelian groups: the sheaf condition transfers
because `forget AddCommGrpCat` preserves limits and reflects isomorphisms. -/
def typeSheaf {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) : X.Sheaf (Type u) :=
  ⟨typePresheaf ℱ.presheaf,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) ℱ.presheaf).1 ℱ.2⟩

/-- The underlying presheaf of `typeSheaf ℱ` is `typePresheaf ℱ.presheaf`. -/
lemma typeSheaf_presheaf {X : TopCat.{u}} (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (typeSheaf ℱ).presheaf = typePresheaf ℱ.presheaf := rfl

end GermPullback

end

end
