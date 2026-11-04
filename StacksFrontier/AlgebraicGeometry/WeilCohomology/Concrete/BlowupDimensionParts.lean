module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcessDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishingGeneral
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowing up in a smooth centre of pure codimension, part by part

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over a field `k`, with `X` not
necessarily equidimensional, such that every irreducible component of `Z` has codimension `r` in
`X` (the hypothesis of [Stacks, Tag 0FIH]). Let `b : X' ⟶ X` be the blowing up of `X` in `Z`,
`j : E ⟶ X'` the exceptional divisor and `π : E ⟶ Z`. Write `X_d`, `X'_d` for the open and
closed parts of dimension `d` (Stacks 02NM). This file proves:

* `b` carries `X'_d` into `X_d`, and `X'_d = b⁻¹(X_d)`;
* `Z ∩ X_d` has dimension `d - r` (and `r ≤ d` when it is nonempty), and `E ∩ X'_d` has dimension
  `d - 1`;
* `π` has relative dimension `r - 1`, `𝒞_{Z/X}` is finite locally free of rank `r`, the excess
  bundle `𝓕` of Tag 0FVA has rank `r - 1`, and `(E, 𝒞_{E/X'})` is a projective tower of fibre
  dimension `r - 1` over `Z`.

These are the statements of `relativeDimension_exceptionalProj`,
`isFiniteLocallyFreeOfRank_centreConormal`, `isFiniteLocallyFreeOfRank_excessConormal` and
`isLocallyProjectiveTower_exceptionalConormal` (namespace
`Stacks.WeilCohomology.SmoothProjectiveScheme`) without the hypothesis that `X` and `Z` are
equidimensional.

## Main results

In namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`:

* `mem_dimPart_blowupObj_iff`.
* `relativeDimension_centrePart`, `le_of_mem_centrePart`.
* `relativeDimension_exceptionalPart`, `relativeDimension_exceptionalPiece`.
* `relativeDimension_exceptionalProj_of_codimension`.
* `isFiniteLocallyFreeOfRank_centreConormal_of_codimension`,
  `isFiniteLocallyFreeOfRank_excessConormal_of_codimension`.
* `isLocallyProjectiveTower_exceptionalConormal_of_codimension`.

In namespace `Stacks.WeilCohomology`:

* `isFiniteLocallyFreeOfRank_conormalSheaf_of_dimPart`.

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-! ### The rank of the conormal sheaf, part by part -/

/-- **The conormal sheaf of an immersion of smooth schemes of pure codimension `c` is finite
locally free of rank `c`**, without assuming the schemes equidimensional: if over each part `X_d`
of `X` of relative dimension `d` the part `ι⁻¹(X_d)` of `Z` has relative dimension `d - c`, with
`c ≤ d` whenever it is nonempty, then `𝒞_{Z/X}` has rank `c`. On `ι⁻¹(X_d)` the conormal sheaf is
that of `ι⁻¹(X_d) ⟶ X_d` (Tag 01R4), of rank `d - (d - c) = c` by Tag 06AA. -/
@[ega "IV 17.10.4" "special case"]
theorem isFiniteLocallyFreeOfRank_conormalSheaf_of_dimPart {Z X S : Scheme.{u}} (ι : Z ⟶ X)
    [IsImmersion ι] (p : X ⟶ S) [Smooth p] [Smooth (ι ≫ p)] (c : ℕ)
    (h : ∀ d : ℕ, RelativeDimension ((ι ⁻¹ᵁ dimPart p d).ι ≫ ι ≫ p) (d - c))
    (hc : ∀ (z : Z) (d : ℕ), ι z ∈ dimPart p d → c ≤ d) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheaf ι) c := by
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ c).1 ?_
  have hcov : (⨆ d, ι ⁻¹ᵁ dimPart p d) = ⊤ :=
    ((isClopenDecomposition_dimPart p).preimage ι).iSup_eq_top
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top
    (fun d ↦ ι ⁻¹ᵁ dimPart p d) hcov fun d ↦ ?_
  rcases isEmpty_or_nonempty (ι ⁻¹ᵁ dimPart p d).toScheme with hE | ⟨⟨z, hz⟩⟩
  · intro x
    exact (IsEmpty.false x).elim
  have hcd : c ≤ d := hc z d hz
  set U := dimPart p d
  have : Smooth ((ι ∣_ U) ≫ U.ι ≫ p) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have hZ : RelativeDimension ((ι ∣_ U) ≫ U.ι ≫ p) (d - c) :=
    relativeDimension_of_eq (by rw [← Category.assoc, ← Category.assoc, morphismRestrict_ι]) (h d)
  have hrank := Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheaf (ι ∣_ U)
    (U.ι ≫ p) (relativeDimension_partBase p d) hZ
  rw [show d - (d - c) = c by omega] at hrank
  have hiso := Stacks.Immersion.isIso_immersionConormalSheafMap_ι ι U
  replace hrank := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ c).2 hrank
  exact Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    (((Scheme.Modules.restrictFunctorIsoPullback (ι ⁻¹ᵁ U).ι).app _) ≪≫
      @asIso _ _ _ _ _ hiso).symm
    hrank

namespace SmoothProjectiveScheme

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]

/-! ### The parts of the blowing up -/

/-- **The blowing up carries the part `X'_d` of `X'` of dimension `d` into the part `X_d` of
`X`.** The open `X'_d ∩ b⁻¹(X_e)` around a point meets the dense open `b⁻¹(X \ Z)`, over which
`b` is an open immersion, and open immersions preserve the parts of constant dimension. -/
theorem blowupHom_mem_dimPart {d : ℕ} {x : (blowupObj i).obj.left}
    (hx : x ∈ dimPart (blowupObj i).obj.hom d) :
    (blowupHom i).hom.left x ∈ dimPart X.obj.hom d := by
  set b := (blowupHom i).hom.left
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart X.obj.hom).exists_mem (b x)
  let W : (blowupObj i).obj.left.Opens :=
    dimPart (blowupObj i).obj.hom d ⊓ b ⁻¹ᵁ dimPart X.obj.hom e
  obtain ⟨u, huW, huD⟩ := (dense_preimage_compl_support i).inter_open_nonempty _ W.2
    ⟨x, hx, he⟩
  let V : (blowupObj i).obj.left.Opens := b ⁻¹ᵁ i.hom.left.ker.support.compl
  have : IsIso (b ∣_ i.hom.left.ker.support.compl) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_compl_support_reesData _
  have : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  let v : V := ⟨u, huD⟩
  have h1 := mem_dimPart_iff_of_isOpenImmersion (V.ι ≫ (blowupObj i).obj.hom)
    (blowupObj i).obj.hom V.ι rfl d v
  have h2 := mem_dimPart_iff_of_isOpenImmersion (V.ι ≫ (blowupObj i).obj.hom) X.obj.hom
    (V.ι ≫ b) (by rw [Category.assoc, Over.w (blowupHom i).hom]) d v
  have hbu : (V.ι ≫ b) v ∈ dimPart X.obj.hom d := h2.1 (h1.2 huW.1)
  have hde := (isClopenDecomposition_dimPart X.obj.hom).eq_of_mem hbu huW.2
  rwa [hde]

/-- **`X'_d = b⁻¹(X_d)`**: a point of `X'` lies in the part of dimension `d` exactly when its image
in `X` does. -/
theorem mem_dimPart_blowupObj_iff (d : ℕ) (x : (blowupObj i).obj.left) :
    x ∈ dimPart (blowupObj i).obj.hom d ↔ (blowupHom i).hom.left x ∈ dimPart X.obj.hom d := by
  refine ⟨blowupHom_mem_dimPart i, fun h ↦ ?_⟩
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart (blowupObj i).obj.hom).exists_mem x
  rwa [(isClopenDecomposition_dimPart X.obj.hom).eq_of_mem (blowupHom_mem_dimPart i he) h] at he

/-- A point of `E` lies over the part `X'_d` of `X'` exactly when its image in `Z` lies over the
part `X_d` of `X`: `b ∘ j = i ∘ π`. -/
theorem exceptionalHom_mem_dimPart_iff (d : ℕ) (t : (exceptionalObj i).obj.left) :
    (exceptionalHom i).hom.left t ∈ dimPart (blowupObj i).obj.hom d ↔
      i.hom.left ((exceptionalProj i).hom.left t) ∈ dimPart X.obj.hom d := by
  rw [mem_dimPart_blowupObj_iff, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    (isPullback_exceptional i).w]

/-! ### The parts of the centre -/

variable {r : ℕ}
  (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
    Order.coheight (i.hom.left z) = r)

omit [IsClosedImmersion i.hom.left] in
include hr in
/-- **The codimension of a nonempty smooth closed subscheme of pure codimension `r` in an
equidimensional `X` of dimension `n` is at most `n`**: at the generic point `η` of a component,
`n = dim \overline{η} + dim 𝒪_{X,η}` (Tag 0A21) and `dim 𝒪_{X,η} = r` (Tag 02IZ). -/
theorem le_of_codimension {n : ℕ} (hX : RelativeDimension X.obj.hom n) [Nonempty Z.obj.left] :
    r ≤ n := by
  obtain ⟨z⟩ := ‹Nonempty Z.obj.left›
  obtain ⟨W, hW, -, -⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k Z.obj.left
      Z.obj.hom z
  have hη : closure ({hW.1.genericPoint} : Set Z.obj.left) = W :=
    (hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)).def
  set η := hW.1.genericPoint
  have h3 := topologicalKrullDimAt_eq_add_ringKrullDim_stalk k X.obj.hom (i.hom.left η)
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k X.obj.hom,
    AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hr η (hη ▸ hW),
    (relativeDimension_iff_forall_topologicalKrullDimAt_of_field X.obj.hom n).1 hX] at h3
  have h4 : n = (Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation k).dimensionFunction X.obj.hom (i.hom.left η)).toNat + r := by
    exact_mod_cast h3
  omega

/-- The local dimension at a point of an open `U` is `n` if `U` has relative dimension `n`. -/
private theorem topologicalKrullDimAt_eq_of_relativeDimension {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] (U : T.Opens) {n : ℕ}
    (h : RelativeDimension (U.ι ≫ q) n) {t : T} (ht : t ∈ U) :
    topologicalKrullDimAt T t = (n : WithBot ℕ∞) := by
  rw [← (relativeDimension_iff_forall_topologicalKrullDimAt_of_field _ n).1 h ⟨t, ht⟩]
  exact (U.isOpen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq (⟨t, ht⟩ : U))

/-- The part `Z ∩ X_d = i⁻¹(X_d)` of `Z` over the part of `X` of dimension `d`. -/
abbrev centrePart (d : ℕ) : Z.obj.left.Opens :=
  i.hom.left ⁻¹ᵁ dimPart X.obj.hom d

include hr in
/-- **`Z ∩ X_d` has dimension `d - r`**: every component of it has codimension `r` in `X_d`. -/
theorem relativeDimension_centrePart (d : ℕ) :
    RelativeDimension ((centrePart i d).ι ≫ Z.obj.hom) (d - r) :=
  relativeDimension_of_codimension (clopenRestrict i _ (isClopen_dimPart X d))
    (relativeDimension_partBase X.obj.hom d)
    (coheight_clopenRestrict i _ (isClopen_dimPart X d) hr)

include hr in
/-- If `Z ∩ X_d` is nonempty then `r ≤ d`. -/
theorem le_of_mem_centrePart {d : ℕ} {z : Z.obj.left} (hz : i.hom.left z ∈ dimPart X.obj.hom d) :
    r ≤ d := by
  have : Nonempty (clopenObj Z (i.hom.left ⁻¹ᵁ dimPart X.obj.hom d)
      (isClopen_preimage i _ (isClopen_dimPart X d))).obj.left := ⟨⟨z, hz⟩⟩
  exact le_of_codimension (clopenRestrict i _ (isClopen_dimPart X d))
    (coheight_clopenRestrict i _ (isClopen_dimPart X d) hr) (relativeDimension_partBase X.obj.hom d)

include hr in
/-- **The local dimension of `Z` at a point over `X_d` is `d - r`.** -/
theorem topologicalKrullDimAt_centre {d : ℕ} {z : Z.obj.left}
    (hz : i.hom.left z ∈ dimPart X.obj.hom d) :
    topologicalKrullDimAt Z.obj.left z = ((d - r : ℕ) : WithBot ℕ∞) :=
  topologicalKrullDimAt_eq_of_relativeDimension Z.obj.hom (centrePart i d)
    (relativeDimension_centrePart i hr d) hz

/-! ### The parts of the exceptional divisor -/

/-- The part `E ∩ X'_d = j⁻¹(X'_d)` of the exceptional divisor over the part of `X'` of
dimension `d`. -/
abbrev exceptionalPart (d : ℕ) : (exceptionalObj i).obj.left.Opens :=
  (exceptionalHom i).hom.left ⁻¹ᵁ dimPart (blowupObj i).obj.hom d

/-- An open piece `A` of the exceptional divisor mapping to `X'_d` by a closed immersion `s`
compatible with `j` has dimension `d - 1`: it is a Cartier divisor in `X'_d`. -/
private theorem relativeDimension_exceptional_comp_of_isOpenImmersion (d : ℕ)
    {A : Scheme.{u}} (a : A ⟶ (exceptionalObj i).obj.left) [IsOpenImmersion a]
    (s : A ⟶ (dimPart (blowupObj i).obj.hom d).toScheme) [IsClosedImmersion s]
    (hs : s ≫ (dimPart (blowupObj i).obj.hom d).ι = a ≫ (exceptionalHom i).hom.left)
    [LocallyOfFiniteType (a ≫ (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom)] :
    RelativeDimension (a ≫ (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom) (d - 1) := by
  refine relativeDimension_of_ringKrullDim_stalk_eq _ (partBase (blowupObj i).obj.hom d) s
    (by rw [partBase, ← Category.assoc, hs, Category.assoc]) (relativeDimension_partBase _ d)
    fun η hη ↦ ?_
  have hgen : a η ∈ genericPoints (exceptionalObj i).obj.left :=
    (Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding a.isOpenEmbedding η).1 hη
  have hpt : (dimPart (blowupObj i).obj.hom d).ι (s η) = (exceptionalHom i).hom.left (a η) := by
    rw [← Scheme.Hom.comp_apply, hs, Scheme.Hom.comp_apply]
  rw [ringKrullDim_stalk_eq_of_etale (dimPart (blowupObj i).obj.hom d).ι, hpt,
    ringKrullDim_stalk_exceptionalHom i _ hgen]
  rfl

/-- **`E ∩ X'_d` has dimension `d - 1`**: it is an effective Cartier divisor in `X'_d`, whose
components have codimension one (Tags 0BCN, 0A21). -/
theorem relativeDimension_exceptionalPart (d : ℕ) :
    RelativeDimension ((exceptionalPart i d).ι ≫ (exceptionalObj i).obj.hom) (d - 1) :=
  relativeDimension_of_eq (by rw [Over.w (exceptionalHom i).hom])
    (relativeDimension_exceptional_comp_of_isOpenImmersion i d (exceptionalPart i d).ι
      ((exceptionalHom i).hom.left ∣_ dimPart (blowupObj i).obj.hom d) (morphismRestrict_ι _ _))

/-- **The local dimension of `E` at a point over `X'_d` is `d - 1`.** -/
theorem topologicalKrullDimAt_exceptional {d : ℕ} {t : (exceptionalObj i).obj.left}
    (ht : (exceptionalHom i).hom.left t ∈ dimPart (blowupObj i).obj.hom d) :
    topologicalKrullDimAt (exceptionalObj i).obj.left t = ((d - 1 : ℕ) : WithBot ℕ∞) :=
  topologicalKrullDimAt_eq_of_relativeDimension (exceptionalObj i).obj.hom (exceptionalPart i d)
    (relativeDimension_exceptionalPart i d) ht

/-- A point of the piece `E ×_{X'} X'_d` of the exceptional divisor lies over the part `X_d`
of `X`. -/
theorem exceptionalPiece_mem_dimPart (d : ℕ)
    (t : (Limits.pullback (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι :
      Scheme.{u})) :
    i.hom.left ((exceptionalProj i).hom.left
      (pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι t)) ∈
      dimPart X.obj.hom d := by
  rw [← exceptionalHom_mem_dimPart_iff]
  have h : (exceptionalHom i).hom.left
      (pullback.fst (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι t) =
      (dimPart (blowupObj i).obj.hom d).ι
        (pullback.snd (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι t) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [h]
  exact (pullback.snd (exceptionalHom i).hom.left (dimPart (blowupObj i).obj.hom d).ι t).2

/-- **The piece `E ×_{X'} X'_d` of the exceptional divisor has dimension `d - 1`**: it is an
effective Cartier divisor in `X'_d`, whose components have codimension one (Tags 0BCN, 0A21). -/
theorem relativeDimension_exceptionalPiece (d : ℕ) :
    RelativeDimension (pullback.fst (exceptionalHom i).hom.left
      (dimPart (blowupObj i).obj.hom d).ι ≫ (exceptionalHom i).hom.left ≫
        (blowupObj i).obj.hom) (d - 1) :=
  relativeDimension_exceptional_comp_of_isOpenImmersion i d _ _ pullback.condition.symm

include hr in
/-- **`π : E ⟶ Z` has relative dimension `r - 1`** for a centre of pure codimension `r ≥ 1`: at a
point of `E` over `X'_d`, the dimension formula of Tag 0AFF reads `d - 1 = (d - r) + (r - 1)`. -/
theorem relativeDimension_exceptionalProj_of_codimension (hr0 : 0 < r) :
    RelativeDimension (exceptionalProj i).hom.left (r - 1) := by
  have : IsLocallyNoetherian (exceptionalObj i).obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (exceptionalObj i).obj.hom
  have : IsLocallyNoetherian Z.obj.left := LocallyOfFiniteType.isLocallyNoetherian Z.obj.hom
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  intro t
  set π := (exceptionalProj i).hom.left
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart (blowupObj i).obj.hom).exists_mem
    ((exceptionalHom i).hom.left t)
  have hz : i.hom.left (π t) ∈ dimPart X.obj.hom d := (exceptionalHom_mem_dimPart_iff i d t).1 hd
  have hrd := le_of_mem_centrePart i hr hz
  have h := topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth π t
  rw [topologicalKrullDimAt_exceptional i hd, topologicalKrullDimAt_centre i hr hz] at h
  generalize ha : d - 1 = a at h
  generalize hb : d - r = b at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, topologicalKrullDimAt (π.fiber (π t)) (π.asFiber t) = m := by
    generalize topologicalKrullDimAt (π.fiber (π t)) (π.asFiber t) = x at h ⊢
    induction x using WithBot.recBotCoe with
    | bot => simp at h
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((a : ℕ∞) : WithBot ℕ∞) = ((((b : ℕ) : ℕ∞) + ⊤ : ℕ∞) :
            WithBot ℕ∞) := by
          exact_mod_cast h
        rw [add_top] at h'
        exact ENat.coe_ne_top _ (WithBot.coe_injective h')
      | coe m => exact ⟨m, rfl⟩
  rw [hm] at h ⊢
  have h' : a = b + m := by exact_mod_cast h
  rw [show r - 1 = m by omega]

/-! ### Ranks -/

include hr in
/-- **`𝒞_{Z/X}` is finite locally free of rank `r`** for a centre of pure codimension `r`. -/
theorem isFiniteLocallyFreeOfRank_centreConormal_of_codimension :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (centreConormal i) r := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  exact isFiniteLocallyFreeOfRank_conormalSheaf_of_dimPart i.hom.left X.obj.hom r
    (fun d ↦ relativeDimension_of_eq (by rw [Over.w i.hom]) (relativeDimension_centrePart i hr d))
    fun z d hz ↦ le_of_mem_centrePart i hr hz

include hr in
/-- **The excess bundle `𝓕` has rank `r - 1`** for a centre of pure codimension `r ≥ 1`. -/
theorem isFiniteLocallyFreeOfRank_excessConormal_of_codimension (hr0 : 0 < r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (excessConormal i)
      (r - 1) := by
  have := isFiniteLocallyFreeOfRank_centreConormal_of_codimension i hr
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (exceptionalProj i).hom.left).obj (centreConormal i))
      (r - 1 + 1) := by
    rw [Nat.sub_add_cancel hr0]
    exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ _
  exact Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (excessConormalMap i) inferInstance (isInvertible_exceptionalConormal i) _ hM

include hr in
/-- **The exceptional divisor with `𝒞_{E/X'}` is a projective tower of fibre dimension `r - 1`
over the centre**, locally on `Z`, for a centre of pure codimension `r ≥ 1` (Tag 0FUT). -/
theorem isLocallyProjectiveTower_exceptionalConormal_of_codimension (hr0 : 0 < r) :
    Stacks.Chow.IsLocallyProjectiveTower (r - 1) (exceptionalProj i).hom.left
      (exceptionalConormal i) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hinv : inv i.hom.left.toImage ≫ i.hom.left = i.hom.left.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι _).symm
  have : Smooth (i.hom.left.ker.subschemeι ≫ X.obj.hom) := by
    rw [← hinv, Category.assoc]
    infer_instance
  have hC := isFiniteLocallyFreeOfRank_conormalSheaf_of_dimPart i.hom.left.ker.subschemeι
    X.obj.hom r (fun d ↦ ?_) (fun z d hz ↦ ?_)
  · have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι) (r - 1 + 1) := by
      rw [Nat.sub_add_cancel hr0]
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        (Stacks.Conormal.conormalDegreeOneIso _) hC
    exact (Stacks.AlgebraicGeometry.isLocallyProjectiveTower_pullbackSnd_blowUpToBase X.obj.hom
      i.hom.left (r - 1)).of_iso_module (exceptionalConormalIso i)
  · -- the part of the centre over `X_d`, read through `Z ≅ i.ker.subscheme`
    have hZ' : RelativeDimension ((centrePart i d).ι ≫ i.hom.left ≫ X.obj.hom) (d - r) :=
      relativeDimension_of_eq (by rw [Over.w i.hom]) (relativeDimension_centrePart i hr d)
    set φ := inv i.hom.left.toImage
    have h := RelativeDimension.of_isPullback (IsPullback.of_horiz_isIso
      (fst := φ ∣_ centrePart i d) (g := 𝟙 (Spec (.of k)))
      (snd := (φ ⁻¹ᵁ centrePart i d).ι ≫ φ ≫ i.hom.left ≫ X.obj.hom)
      (f := (centrePart i d).ι ≫ i.hom.left ≫ X.obj.hom)
      ⟨by rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, Category.assoc]⟩) hZ'
    have hU : i.hom.left.ker.subschemeι ⁻¹ᵁ dimPart X.obj.hom d = φ ⁻¹ᵁ centrePart i d := by
      rw [← hinv]; ext x; exact Iff.rfl
    have key : ∀ (W : (i.hom.left.ker.subscheme : Scheme.{u}).Opens), W = φ ⁻¹ᵁ centrePart i d →
        ∀ (q : (i.hom.left.ker.subscheme : Scheme.{u}) ⟶ Spec (.of k)) [LocallyOfFiniteType q],
        q = φ ≫ i.hom.left ≫ X.obj.hom → RelativeDimension (W.ι ≫ q) (d - r) := by
      rintro W rfl q _ rfl; exact h
    exact key _ hU _ (by rw [← hinv, Category.assoc])
  · have hz' : i.hom.left (inv i.hom.left.toImage z) ∈ dimPart X.obj.hom d := by
      rw [← Scheme.Hom.comp_apply, hinv]; exact hz
    exact le_of_mem_centrePart i hr hz'

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
