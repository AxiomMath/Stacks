module

public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.Glue

/-!
# Discharging the agreement hypothesis of the submodule glueing step

`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean` glues a family `N : ι →
F.Submodule` of submodules of a fixed `𝒪_X`-module along a family `W : ι → X.Opens` of opens,
under the hypothesis `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.Agree W N`: the pieces agree
over every open contained in two members of the family. The hypothesis is a real condition —
without it `glue` is an intersection rather than a glueing and `glue_obj_of_le` is false — and it
is left open by all four theorems of
`StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/Glue.lean`. This file discharges it.

## Main results

* `coRestrict_restrictTo_obj_of_le`: **the content.** For an open immersion `f` and an open `V`
  of `X` inside the range of `f`, the co-restriction of the restriction of `M` has the same
  sections over `V` as `M` itself. So over the opens inside a member of the family, co-restricting
  a restriction changes nothing, which is what makes the agreement hypothesis provable at all.
* `agree_of_obj_eq`: agreement from a common ambient submodule — if each piece has the sections
  of one `M : F.Submodule` over the opens inside its own member, the family agrees.
* `agree_coRestrict_restrictTo` and `agree_coRestrict_of_restrictTo_eq`: the two previous results
  composed, for a family of the shape `fun i => coRestrict (W i).ι (P i)`, which is the shape
  `Stacks.AlgebraicGeometry.SubmodulePrimitives.glueOfRestricted` consumes.
* `agree_pair`: **agreement for a two-member family**, which is the family the affine induction of
  [Stacks, Tag 01PF] actually glues: `Agree` for it is exactly the statement that the two pieces
  have the same sections over the opens inside the intersection of their two members.

## What this measures about the obligation

The agreement hypothesis is *not* an independent obligation of the induction of
[Stacks, Tag 01PF], and the glueing step cannot discharge it on its own. For the two-member
family `![U, V]` of the source's reduction — the given subsheaf over the quasi-compact open `U`
and the subsheaf produced over the affine open `V` — `agree_pair` shows that `Agree` unfolds to

> for every open `Z ≤ U ⊓ V`, the two pieces have the same sections over `Z`,

which is precisely the conclusion `\mathcal{G}'|_{U \cap V} = \mathcal{G}|_{U \cap V}` that the
source's affine case is required to deliver. Agreement is therefore discharged *by* that case and
not before it: what the induction owes is the affine case in the form that prescribes the
subsheaf over the overlap, which is a strictly stronger statement than
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on` (the
special case where the prescribed subsheaf is all of `F`).

`coRestrict_restrictTo_obj_of_le` is the part that is genuinely about the glueing step and is
reusable independently: it says the co-restriction primitive of
`StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/CoRestrict.lean` loses no information over
the opens where the information lives, so a family of pieces that are visibly restrictions of one
ambient submodule always satisfies the hypothesis.

## Implementation notes

The proof of `coRestrict_restrictTo_obj_of_le` uses no transport along an equality of opens, and
that is the only measurement in this file. The obvious argument instantiates the quantifier of
`Stacks.AlgebraicGeometry.SubmodulePrimitives.mem_coRestrict_iff` at `f ⁻¹ᵁ V` and then needs
`f ''ᵁ f ⁻¹ᵁ V = V`, whose two sides index the module the section lives in, so the comparison
would need an `eqToHom`. Instead the membership is obtained from *locality of `M`*: the single
open `f ''ᵁ f ⁻¹ᵁ V` is below `V` by `AlgebraicGeometry.Scheme.Hom.image_preimage_le`, and it
contains every point of `V` by
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf` together with the hypothesis
`V ≤ f.opensRange`, so it is a one-member covering of `V` and the sheaf condition closes the
goal. Only the *inequality* and a *pointwise* membership are used, and neither transports
anything.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** Nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag: this is the discharge of a hypothesis of a step of that
lemma's affine induction.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmoduleAgree

open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.SubmodulePrimitives

variable {Y X : Scheme.{u}} {F : X.Modules}

/-! ### One image open covers every open below -/

/-- For `Z` inside the range of an open immersion `f`, `f ''ᵁ (f ⁻¹ᵁ Z)` contains every point
of `Z`. -/
private theorem mem_image_preimage_of_le_opensRange (f : Y ⟶ X) [IsOpenImmersion f]
    {Z : X.Opens} (hZ : Z ≤ f.opensRange) {x : X} (hx : x ∈ Z) : x ∈ f ''ᵁ (f ⁻¹ᵁ Z) :=
  (Scheme.Hom.image_preimage_eq_opensRange_inf f Z).symm ▸ (⟨hZ hx, hx⟩ : x ∈ f.opensRange ⊓ Z)

/-- A section over `Z ≤ f.opensRange` lies in `M` once its restriction to the image open
`f ''ᵁ (f ⁻¹ᵁ Z)` does, since that open is a one-member covering of `Z`. -/
private theorem mem_of_restrict_image_preimage_mem (f : Y ⟶ X) [IsOpenImmersion f]
    (M : F.Submodule) {Z : X.Opens} (hZ : Z ≤ f.opensRange) {s : Γ(F, Z)}
    (hs : F.presheaf.map (homOfLE (f.image_preimage_le Z)).op s ∈ M.obj (op (f ''ᵁ (f ⁻¹ᵁ Z)))) :
    s ∈ M.obj (op Z) :=
  M.isSheaf s fun _ hx => ⟨_, homOfLE (f.image_preimage_le Z), hs,
    mem_image_preimage_of_le_opensRange f hZ hx⟩

/-- For `Z ≤ W`, the image open `W.ι ''ᵁ (W.ι ⁻¹ᵁ Z)` contains every point of `Z`. Together with
`AlgebraicGeometry.Scheme.Hom.image_preimage_le` it is therefore a one-member covering of `Z`,
which is how every statement below avoids the equality of opens `W.ι ''ᵁ (W.ι ⁻¹ᵁ Z) = Z` — an
equality that indexes the module its sections live in, so using it would need an `eqToHom`. -/
theorem mem_image_preimage_of_le {W Z : X.Opens} (hZ : Z ≤ W) {x : X} (hx : x ∈ Z) :
    x ∈ W.ι ''ᵁ (W.ι ⁻¹ᵁ Z) :=
  mem_image_preimage_of_le_opensRange W.ι (by rw [W.opensRange_ι]; exact hZ) hx

/-! ### The restriction to `W` determines the sections over the opens below `W` -/

/-- **Two submodules with the same restriction to `W` have the same sections over every open
inside `W`.** This is the bridge between the two currencies the induction of [Stacks, Tag 01PF]
mixes: its property transfers speak of `Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo`,
while the agreement hypothesis of the glueing step speaks of the sections over the opens of `X`,
and this is what turns the first into the second.

The equality of sections holds at the image opens by definition
(`Stacks.AlgebraicGeometry.SubmoduleRestrict.mem_restrictTo` is `Iff.rfl`); an arbitrary open
below `W` is covered by one image open, by `mem_image_preimage_of_le`, so locality of the two
submodules finishes. -/
theorem obj_eq_of_restrictTo_eq {W : X.Opens} {N M : F.Submodule}
    (h : restrictTo W.ι N = restrictTo W.ι M) {Z : X.Opens} (hZ : Z ≤ W) :
    N.obj (op Z) = M.obj (op Z) := by
  have key : ∀ x : Γ(F, W.ι ''ᵁ (W.ι ⁻¹ᵁ Z)),
      (x ∈ N.obj (op (W.ι ''ᵁ (W.ι ⁻¹ᵁ Z)))) = (x ∈ M.obj (op (W.ι ''ᵁ (W.ι ⁻¹ᵁ Z)))) :=
    fun x => congrArg (fun Q : (F.restrict W.ι).Submodule => x ∈ Q.obj (op (W.ι ⁻¹ᵁ Z))) h
  have hW : Z ≤ W.ι.opensRange := by rw [W.opensRange_ι]; exact hZ
  exact SetLike.ext fun s => ⟨fun hs => mem_of_restrict_image_preimage_mem W.ι M hW
      (Eq.mp (key _) (N.map_mem (homOfLE (W.ι.image_preimage_le Z)).op hs)),
    fun hs => mem_of_restrict_image_preimage_mem W.ι N hW
      (Eq.mpr (key _) (M.map_mem (homOfLE (W.ι.image_preimage_le Z)).op hs))⟩

/-! ### Co-restricting a restriction changes nothing inside the range -/

/-- **Over an open inside the range of `f`, the co-restriction of the restriction of `M` has the
sections of `M`.** The co-restriction imposes no condition away from the range of `f`
(`Stacks.AlgebraicGeometry.SubmodulePrimitives.coRestrict`), so this is the best that can be said
— but it is exactly what the agreement hypothesis of the glueing step asks about, since that
hypothesis only ever looks at opens inside a member of the family. -/
theorem coRestrict_restrictTo_obj_of_le (f : Y ⟶ X) [IsOpenImmersion f] (M : F.Submodule)
    {V : X.Opens} (hV : V ≤ f.opensRange) :
    (coRestrict f (restrictTo f M)).obj (op V) = M.obj (op V) := by
  refine SetLike.ext fun s => ⟨fun hs => ?_, fun hs V' h => ?_⟩
  · exact mem_of_restrict_image_preimage_mem f M hV (hs (f ⁻¹ᵁ V) (f.image_preimage_le V))
  · exact M.map_mem (homOfLE h).op hs

/-- `coRestrict_restrictTo_obj_of_le` for the inclusion of an open subscheme, which is the form
the glueing step uses: the range of `W.ι` is `W`. -/
theorem coRestrict_restrictTo_obj_of_le_opens (W : X.Opens) (M : F.Submodule) {V : X.Opens}
    (hVW : V ≤ W) :
    (coRestrict W.ι (restrictTo W.ι M)).obj (op V) = M.obj (op V) :=
  coRestrict_restrictTo_obj_of_le W.ι M (by rw [W.opensRange_ι]; exact hVW)

/-! ### Agreement -/

/-- **Agreement from a common ambient submodule.** If every piece agrees with one submodule `M`
of `F` over the opens inside its own member of the family, the family satisfies the agreement
hypothesis. -/
theorem agree_of_obj_eq {ι : Type*} (W : ι → X.Opens) (N : ι → F.Submodule) (M : F.Submodule)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ W i → (N i).obj (op V) = M.obj (op V)) : Agree W N :=
  fun i j V hi hj => (h i V hi).trans (h j V hj).symm

/-- **The co-restrictions of the restrictions of one submodule agree.** -/
theorem agree_coRestrict_restrictTo {ι : Type*} (W : ι → X.Opens) (M : F.Submodule) :
    Agree W fun i => coRestrict (W i).ι (restrictTo (W i).ι M) :=
  agree_of_obj_eq W _ M fun i _ hV => coRestrict_restrictTo_obj_of_le_opens (W i) M hV

/-- **Agreement for a family of co-restricted pieces that are the restrictions of one ambient
submodule.** This is the hypothesis of
`Stacks.AlgebraicGeometry.SubmodulePrimitives.restrictTo_glueOfRestricted` and of the three
property transfers beside it, discharged. -/
theorem agree_coRestrict_of_restrictTo_eq {ι : Type*} (W : ι → X.Opens)
    (P : ∀ i, (F.restrict (W i).ι).Submodule) (M : F.Submodule)
    (hP : ∀ i, P i = restrictTo (W i).ι M) :
    Agree W fun i => coRestrict (W i).ι (P i) :=
  agree_of_obj_eq W _ M fun i _ hV => by
    rw [hP i]; exact coRestrict_restrictTo_obj_of_le_opens (W i) M hV

/-! ### The two-member family of the affine induction -/

/-- The two-member family of opens `{U, V}`.

The index type is `ULift Bool` and not `Bool`, and that is forced rather than decorative: the
finite-type locality theorem the glueing step goes through
(`AlgebraicGeometry.Modules.isFiniteType_of_restrict`, and hence
`Stacks.AlgebraicGeometry.SubmoduleGlueLocality.isFiniteType_glue`) indexes its covering by a
`Type u`, where `u` is the universe of the scheme, while `Bool` is in `Type 0`. -/
def pairOpens (U V : X.Opens) : ULift.{u} Bool → X.Opens :=
  fun b => bif b.down then V else U

/-- The two-member family of pieces `{N₀, N₁}`, indexed compatibly with `pairOpens`. -/
def pairPieces (N₀ N₁ : F.Submodule) : ULift.{u} Bool → F.Submodule :=
  fun b => bif b.down then N₁ else N₀

/-- The member of the family `pairOpens U V` at index `false` is `U`. -/
@[simp] theorem pairOpens_up_false (U V : X.Opens) :
    pairOpens U V (ULift.up false) = U := rfl

/-- The member of the family `pairOpens U V` at index `true` is `V`. -/
@[simp] theorem pairOpens_up_true (U V : X.Opens) :
    pairOpens U V (ULift.up true) = V := rfl

/-- The member of the family `pairPieces N₀ N₁` at index `false` is `N₀`. -/
@[simp] theorem pairPieces_up_false (N₀ N₁ : F.Submodule) :
    pairPieces N₀ N₁ (ULift.up false) = N₀ := rfl

/-- The member of the family `pairPieces N₀ N₁` at index `true` is `N₁`. -/
@[simp] theorem pairPieces_up_true (N₀ N₁ : F.Submodule) :
    pairPieces N₀ N₁ (ULift.up true) = N₁ := rfl

/-- **Agreement for a two-member family.** The family glued by the reduction step of
[Stacks, Tag 01PF] has two members — the quasi-compact open `U` carrying the given subsheaf and
the affine open `V` carrying the subsheaf produced on it — and for such a family the agreement
hypothesis is exactly that the two pieces have the same sections over the opens inside `U ⊓ V`.

So the hypothesis is not an independent obligation: it *is* the conclusion
`𝒢'|_{U ⊓ V} = 𝒢|_{U ⊓ V}` that the affine case of the source's proof has to produce. -/
theorem agree_pair {U V : X.Opens} {N₀ N₁ : F.Submodule}
    (h : ∀ Z : X.Opens, Z ≤ U → Z ≤ V → N₀.obj (op Z) = N₁.obj (op Z)) :
    Agree (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁) := by
  rintro ⟨i⟩ ⟨j⟩ Z hi hj
  cases i <;> cases j
  · rfl
  · exact h Z hi hj
  · exact (h Z hj hi).symm
  · rfl

/-- **Agreement for a two-member family, from the restriction identity over the overlap.** This
is the shape the affine induction of [Stacks, Tag 01PF] produces its hypothesis in: the affine
case is applied over `V` to the restriction of the given subsheaf to `U ⊓ V` and returns a
subsheaf whose restriction to `U ⊓ V` is that one again, as an equality of submodules of
`F.restrict (U ⊓ V).ι` — and `obj_eq_of_restrictTo_eq` turns that into the sections-level
agreement `agree_pair` needs. **This is the agreement hypothesis of all four theorems of
`StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/Glue.lean`, discharged.** -/
theorem agree_pair_of_restrictTo_inf_eq {U V : X.Opens} {N₀ N₁ : F.Submodule}
    (h : restrictTo (U ⊓ V).ι N₀ = restrictTo (U ⊓ V).ι N₁) :
    Agree (pairOpens.{u} U V) (pairPieces.{u} N₀ N₁) :=
  agree_pair fun _ hU hV => obj_eq_of_restrictTo_eq h (le_inf hU hV)

/-- The two members of `pairOpens` cover `U ⊔ V`. -/
theorem iSup_pairOpens (U V : X.Opens) : ⨆ b, pairOpens.{u} U V b = U ⊔ V := by
  refine le_antisymm (iSup_le ?_) (sup_le ?_ ?_)
  · rintro ⟨b⟩; cases b
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup_of_le (ULift.up false) le_rfl
  · exact le_iSup_of_le (ULift.up true) le_rfl

end Stacks.AlgebraicGeometry.SubmoduleAgree

end
