module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescentStalk
public import StacksFrontier.AlgebraicGeometry.FieldToResidue

/-!
# The derivation a vector field induces on a stalk of the direct image

Let `ν : Y ⟶ X` be a morphism of schemes over a field `k` and let `D'` be a vector field on `Y`,
that is, a `k`-derivation of `𝒪_Y` in the sense of Tag 0E66. For a point `x` of `X` the stalk
`A' = (ν_* 𝒪_Y)_x` carries a `k`-derivation induced by `D'`: the germ at `x` of a local section
`z` of `ν_* 𝒪_Y` is sent to the germ of `D' z`.

This is the one construction standing between the sheaf-level descent machinery of
`Stacks.Curves.preserves_of_germ_mem_range` — which asks that the germ of `D' (ν^♯ s)` lie in the
image of `𝒪_{X, x}` — and the local ring-theoretic statements of
`Stacks.Curves.mem_range_algebraMap_of_fixes`, which are about a `Derivation k A' A'`.

## Main definitions

* `Stacks.Curves.stalkFun` — the underlying map of the induced derivation.
* `Stacks.Curves.directImageStalkAlgebra` — `(ν_* 𝒪_Y)_x` as an `𝒪_{X, x}`-algebra.
* `Stacks.Curves.directImageStalkFieldAlgebra` — `(ν_* 𝒪_Y)_x` as a `k`-algebra.
* `Stacks.Curves.stalkDerivation` — the induced `k`-derivation of `(ν_* 𝒪_Y)_x`.

## Main results

* `Stacks.Curves.stalkDerivation_germ` — the induced derivation sends the germ of `s` to the germ
  of `D' s`; this is the defining property, and the only one its consumers use.
* `Stacks.Curves.stalkFun_add`, `Stacks.Curves.stalkFun_mul`,
  `Stacks.Curves.stalkFun_structureMap` — additivity, the Leibniz rule and the vanishing on the
  base, the three facts the derivation is assembled from.

## Implementation notes

This is *not* a descent of ring maps along the colimit computing the stalk: `D'` is only additive
over each open, so there is no morphism of presheaves of rings to apply `colimit.desc` to. The
map is instead defined by choosing a representative of the germ
(`TopCat.Presheaf.exists_germ_eq`), and is well defined because two representatives agree on a
smaller open (`TopCat.Presheaf.germ_eq`) on which `D'` commutes with restriction
(`Stacks.Curves.SheafDerivationOf.onSections_map`, the `d_map` field of a derivation read at an
arbitrary inclusion rather than at a `CategoryTheory.homOfLE`).

Additivity and the Leibniz rule need two germs to be represented over *one* open, which is
`Stacks.Curves.exists_germ_eq_pair`: `TopCat.Presheaf.exists_le_germ_eq` produces the second
representative already inside the domain of the first, so no intersection of opens has to be
formed.

The `k`-algebra structure is the germ of the pullback of a global section of the base, written
through `hX ⁻¹ᵁ ⊤` rather than through `Scheme.Hom.appTop` and `⊤`. The two differ only by the
definitional identification of `ν ⁻¹ᵁ ⊤` with `⊤`, which the elaborator does not perform while
checking the *statement* of a lemma, so a section of `Γ(Y, ⊤)` is not accepted where a section of
`(ν_* 𝒪_Y)(⊤)` is wanted. Keeping the preimage explicit avoids that, and
`AlgebraicGeometry.Scheme.Hom.comp_app` — which is `rfl` — then identifies the two-step pullback
with `(ν ≫ hX)^♯`, which is what `Stacks.Curves.SheafDerivationOf.onSections_app` annihilates.
This is the same route `Stacks.Curves.Preserves.descendSection_app` takes.

No compatibility between the `k`-algebra structures on `𝒪_{X, x}` and on `(ν_* 𝒪_Y)_x` is
recorded, because none is needed: the criteria of
`Stacks.Curves.mem_range_iff_of_isCoatom` and `Stacks.Curves.mem_range_of_fixes_of_isCoatom` use
the two structures separately and no scalar tower between them.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

namespace SheafDerivationOf

variable {Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)}

/-- A vector field commutes with every restriction map of the structure sheaf. -/
theorem onSections_map (D : SheafDerivationOf g) {U V : Y.Opens} (f : op U ⟶ op V)
    (s : Γ(Y, U)) :
    D.onSections ((Y.presheaf.map f).hom s) = (Y.presheaf.map f).hom (D.onSections s) :=
  D.d_map (X := op U) (Y := op V) f s

end SheafDerivationOf

section Stalk

variable {X Y : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- Two germs at a point are the germs of two sections over one open. -/
theorem exists_germ_eq_pair (F : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (z w : F.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
      F.germ U x hx s = z ∧ F.germ U x hx t = w := by
  obtain ⟨U₁, h₁, s, hs⟩ := F.exists_germ_eq z
  obtain ⟨U, hU, h, t, ht⟩ := F.exists_le_germ_eq w h₁
  exact ⟨U, h, (F.map (homOfLE hU).op).hom s, t,
    (F.germ_res_apply (homOfLE hU) x h s).trans hs, ht⟩

/-- The germ of the value of `D'` on a representative does not depend on the representative:
two representatives agree on a smaller open, and `D'` commutes with restriction. -/
theorem exists_germ_onSections (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) {x : X}
    (z : (ν.base _* Y.presheaf).stalk x) :
    ∃ w : (ν.base _* Y.presheaf).stalk x, ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)),
      (ν.base _* Y.presheaf).germ U x hx s = z →
        (ν.base _* Y.presheaf).germ U x hx (D'.onSections s) = w := by
  obtain ⟨U₀, hx₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq (ν.base _* Y.presheaf) z
  refine ⟨(ν.base _* Y.presheaf).germ U₀ x hx₀ (D'.onSections s₀), fun U hx s hs => ?_⟩
  obtain ⟨W, hxW, iU, iU₀, heq⟩ :=
    (ν.base _* Y.presheaf).germ_eq x hx hx₀ s s₀ (hs.trans hs₀.symm)
  refine TopCat.Presheaf.germ_ext _ W hxW iU iU₀ ?_
  have hres : ∀ {V : X.Opens} (i : W ⟶ V) (t : Γ(Y, ν ⁻¹ᵁ V)),
      ((ν.base _* Y.presheaf).map i.op).hom (D'.onSections t) =
        D'.onSections (((ν.base _* Y.presheaf).map i.op).hom t) :=
    fun i t => (D'.onSections_map ((Opens.map ν.base).map i).op t).symm
  exact (hres iU s).trans ((congrArg _ heq).trans (hres iU₀ s₀).symm)

/-- The endomorphism of the stalk `(ν_* 𝒪_Y)_x` induced by a vector field `D'` on `Y`: the germ
of a section is sent to the germ of the value of `D'` on it. -/
def stalkFun (ν : Y ⟶ X) {hX : X ⟶ Spec (.of k)} (D' : SheafDerivationOf (ν ≫ hX)) {x : X}
    (z : (ν.base _* Y.presheaf).stalk x) : (ν.base _* Y.presheaf).stalk x :=
  (exists_germ_onSections ν D' z).choose

/-- `Stacks.Curves.stalkFun` sends the germ of `s` to the germ of `D' s`. -/
theorem stalkFun_germ (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) {x : X} (U : X.Opens)
    (hx : x ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)) :
    stalkFun ν D' ((ν.base _* Y.presheaf).germ U x hx s) =
      (ν.base _* Y.presheaf).germ U x hx (D'.onSections s) :=
  ((exists_germ_onSections ν D' _).choose_spec U hx s rfl).symm

/-- `Stacks.Curves.stalkFun` is additive. -/
theorem stalkFun_add (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) {x : X}
    (z w : (ν.base _* Y.presheaf).stalk x) :
    stalkFun ν D' (z + w) = stalkFun ν D' z + stalkFun ν D' w := by
  obtain ⟨U, hx, s, t, hs, ht⟩ := exists_germ_eq_pair (ν.base _* Y.presheaf) x z w
  subst hs ht
  rw [← map_add, stalkFun_germ, stalkFun_germ, stalkFun_germ, SheafDerivationOf.onSections_add,
    map_add]

/-- `Stacks.Curves.stalkFun` satisfies the Leibniz rule. -/
theorem stalkFun_mul (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) {x : X}
    (z w : (ν.base _* Y.presheaf).stalk x) :
    stalkFun ν D' (z * w) = z * stalkFun ν D' w + w * stalkFun ν D' z := by
  obtain ⟨U, hx, s, t, hs, ht⟩ := exists_germ_eq_pair (ν.base _* Y.presheaf) x z w
  subst hs ht
  rw [← map_mul, stalkFun_germ, stalkFun_germ, stalkFun_germ, SheafDerivationOf.onSections_mul,
    map_add, map_mul, map_mul]

/-- `Stacks.Curves.stalkFun` sends `1` to `0`. -/
theorem stalkFun_one (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) (x : X) :
    stalkFun ν D' (1 : (ν.base _* Y.presheaf).stalk x) = 0 := by
  have h := stalkFun_mul ν D' (1 : (ν.base _* Y.presheaf).stalk x) 1
  rw [mul_one, one_mul] at h
  have h2 : stalkFun ν D' (1 : (ν.base _* Y.presheaf).stalk x) + 0 =
      stalkFun ν D' (1 : (ν.base _* Y.presheaf).stalk x) +
        stalkFun ν D' (1 : (ν.base _* Y.presheaf).stalk x) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The stalk at `x` of `ν_* 𝒪_Y` as an algebra over the local ring of `X` at `x`, through the
comparison map of stalks of `ν^♯`. For the normalization of a reduced scheme this is
`AlgebraicGeometry.Scheme.normalizationPushforwardStalkAlgebra`. -/
@[instance_reducible]
def directImageStalkAlgebra (ν : Y ⟶ X) (x : X) :
    Algebra (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ν.c).hom.toAlgebra

/-- The stalk at `x` of `ν_* 𝒪_Y` as a `k`-algebra, through the structure morphism of `Y`
factored as `ν` followed by that of `X`: a global section of the base is pulled back to `X`,
then to `Y`, and its germ taken. -/
@[instance_reducible]
def directImageStalkFieldAlgebra (ν : Y ⟶ X) (hX : X ⟶ Spec (.of k)) (x : X) :
    Algebra k ((ν.base _* Y.presheaf).stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ hX.app ⊤ ≫ ν.app (hX ⁻¹ᵁ ⊤) ≫
    (ν.base _* Y.presheaf).germ (hX ⁻¹ᵁ ⊤) x trivial).hom.toAlgebra

/-- A vector field on `Y` annihilates the germ of a section pulled back from the base. -/
theorem stalkFun_structureMap (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) (x : X)
    (hx : x ∈ hX ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)) (b : Γ(Spec (.of k), ⊤)) :
    stalkFun ν D' ((ν.base _* Y.presheaf).germ (hX ⁻¹ᵁ ⊤) x hx
        ((ν.app (hX ⁻¹ᵁ ⊤)).hom ((hX.app ⊤).hom b))) = 0 := by
  have h2 : D'.onSections ((ν.app (hX ⁻¹ᵁ ⊤)).hom ((hX.app ⊤).hom b)) = 0 :=
    D'.onSections_app ⊤ b
  rw [stalkFun_germ, h2, map_zero]

/-- **The derivation induced on a stalk of the direct image.** A vector field `D'` on `Y` — a
`k`-derivation of `𝒪_Y` in the sense of Tag 0E66 — induces a `k`-derivation of the stalk
`A' = (ν_* 𝒪_Y)_x`, sending the germ at `x` of a local section `z` of `ν_* 𝒪_Y` to the germ of
`D' z`.

This is not the descent of a morphism of rings along a colimit: `D'` is only additive over each
open, so the construction is by choice of a representative of the germ, well defined because two
representatives agree on a smaller open and `D'` commutes with restriction. -/
def stalkDerivation (ν : Y ⟶ X) {hX : X ⟶ Spec (.of k)} (D' : SheafDerivationOf (ν ≫ hX))
    (x : X) :
    letI := directImageStalkFieldAlgebra ν hX x
    Derivation k ((ν.base _* Y.presheaf).stalk x) ((ν.base _* Y.presheaf).stalk x) :=
  letI := directImageStalkFieldAlgebra ν hX x
  { toFun := stalkFun ν D'
    map_add' := stalkFun_add ν D'
    map_smul' := fun c z => by
      change stalkFun ν D' (c • z) = c • stalkFun ν D' z
      have h0 : stalkFun ν D' (algebraMap k ((ν.base _* Y.presheaf).stalk x) c) = 0 :=
        stalkFun_structureMap ν D' x trivial (((Scheme.ΓSpecIso (.of k)).inv).hom c)
      rw [Algebra.smul_def, stalkFun_mul, h0, mul_zero, add_zero, Algebra.smul_def]
    map_one_eq_zero' := stalkFun_one ν D' x
    leibniz' := fun z w => by
      change stalkFun ν D' (z * w) = z • stalkFun ν D' w + w • stalkFun ν D' z
      rw [stalkFun_mul, smul_eq_mul, smul_eq_mul] }

/-- The induced derivation on the stalk sends the germ of `s` to the germ of `D' s`. -/
theorem stalkDerivation_germ (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX)) {x : X}
    (U : X.Opens) (hx : x ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)) :
    letI := directImageStalkFieldAlgebra ν hX x
    stalkDerivation ν D' x ((ν.base _* Y.presheaf).germ U x hx s) =
      (ν.base _* Y.presheaf).germ U x hx (D'.onSections s) :=
  stalkFun_germ ν D' U hx s

/-- **Descending a vector field is a condition on the induced derivations of the stalks.** If,
at every point `x` of `X`, the derivation that `D'` induces on `(ν_* 𝒪_Y)_x` carries the image of
`𝒪_{X, x}` into itself, then `D'` preserves `ν^♯ 𝒪_X` and hence descends.

This is `Stacks.Curves.preserves_of_germ_mem_range` with the germ of `D' (ν^♯ s)` rewritten, by
`Stacks.Curves.stalkDerivation_germ`, as the value of the induced derivation on the image of the
germ of `s`. -/
theorem preserves_of_stalkDerivation_mem_range (ν : Y ⟶ X)
    (D' : SheafDerivationOf (ν ≫ hX))
    (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom)
    (h : ∀ x : X,
      letI := directImageStalkAlgebra ν x
      letI := directImageStalkFieldAlgebra ν hX x
      ∀ a : X.presheaf.stalk x,
        stalkDerivation ν D' x
            (algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x) a) ∈
          Set.range (algebraMap (X.presheaf.stalk x)
            ((ν.base _* Y.presheaf).stalk x))) :
    Preserves ν D' := by
  refine preserves_of_germ_mem_range D' hinj fun U s x hx => ?_
  let := directImageStalkAlgebra ν x
  let := directImageStalkFieldAlgebra ν hX x
  have hg : (ν.base _* Y.presheaf).germ U x hx ((ν.app U).hom s) =
      algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)
        ((X.presheaf.germ U x hx).hom s) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ν.c s).symm
  have key := h x ((X.presheaf.germ U x hx).hom s)
  rw [← hg, stalkDerivation_germ] at key
  exact key

end Stalk

end Stacks.Curves

end
