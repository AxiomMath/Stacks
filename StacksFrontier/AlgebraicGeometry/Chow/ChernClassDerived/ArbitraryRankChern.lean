module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The total Chern class of a finite locally free module of arbitrary rank

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be a finite locally free
`𝒪_X`-module whose rank need not be constant. Following [Stacks, Tag 0ESW], write

  `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …`

for the decomposition of `X` into the open and closed loci where the rank of `ℰ` is `r`
(`Stacks.Chow.rankLociFamily`). On `X_r` the module `ℰ|_{X_r}` has constant rank `r`, so it has the
total Chern class `c(ℰ|_{X_r}) = 1 + c_1(ℰ|_{X_r}) + ⋯ + c_r(ℰ|_{X_r})` of
[Stacks, Tag 0B7H], and by [Stacks, Tag 0FDZ] in every degree there is a unique total class
`c(ℰ) = c_0(ℰ) + c_1(ℰ) + c_2(ℰ) + ⋯` on `X` restricting to it on each `X_r`. It may be nonzero
in infinitely many degrees.

## Main definitions

* `Stacks.Chow.totalChernOfFiniteLocallyFree` — **Stacks 0ESW**, the total Chern class `c(ℰ)`.

## Main results

* `Stacks.Chow.res_totalChernOfFiniteLocallyFree_rankLocus` — its restriction to `X_r` is
  `c(ℰ|_{X_r})`.
* `Stacks.Chow.res_totalChernOfFiniteLocallyFree_of_rank` — more generally, for every
  `h : X' ⟶ X` along which `h^*ℰ` has constant rank `r`, `res_h c(ℰ) = c(h^*ℰ)`.
* `Stacks.Chow.op_totalChernOfFiniteLocallyFree_of_rank` — on such a test scheme `h`, `c(ℰ)`
  operates as `c(h^*ℰ)`: its index-`j` component is `c_j(h^*ℰ) ∩ -`.
* `Stacks.Chow.totalChernOfFiniteLocallyFree_eq_totalChern` — on a module of constant rank it is
  the total Chern class of Stacks 0B7H.
* `Stacks.Chow.res_totalChernOfFiniteLocallyFree` — `res_h c(ℰ) = c(h^*ℰ)` for every `h`.
* `Stacks.Chow.totalChernOfFiniteLocallyFree_congr`,
  `Stacks.Chow.isUnit_totalChernOfFiniteLocallyFree`.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- The pullback of a finite locally free module along a morphism of schemes is finite locally
free, at the spelling `Scheme.Modules.pullback`. -/
theorem isFiniteLocallyFree_pullbackObj {X' : Scheme.{u}} (h : X' ⟶ X) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback h).obj F) :=
  isFiniteLocallyFree_pullback h F hF

/-- **Stacks 0ESW, the total Chern class of a finite locally free module of arbitrary rank.** The
total Chow cohomology class `c(ℰ) = c_0(ℰ) + c_1(ℰ) + ⋯` whose restriction to the rank-`r` locus
`X_r` is the total Chern class `c(ℰ|_{X_r})` of the constant-rank module `ℰ|_{X_r}`, assembled
by Stacks 0FDZ in every degree. -/
def totalChernOfFiniteLocallyFree : TotalChowClass C sX :=
  TotalChowClass.glue (isClopenDecomposition_rankLociFamily F) fun r ↦
    letI := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
    totalChern C ((rankLociFamily F r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down

/-- **The restriction of `c(ℰ)` to the rank locus `X_r`** is `c(ℰ|_{X_r})`. -/
theorem res_totalChernOfFiniteLocallyFree_rankLocus (r : ULift.{u} ℕ) :
    letI := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
    TotalChowClass.res (rankLociFamily F r).ι rfl (totalChernOfFiniteLocallyFree C sX F) =
      totalChern C ((rankLociFamily F r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down :=
  TotalChowClass.res_glue (isClopenDecomposition_rankLociFamily F) _ r

/-- **Characterization of `c(ℰ)`.** For every `h : X' ⟶ X` locally of finite type along which
`h^*ℰ` has constant rank `s`, the restriction of `c(ℰ)` along `h` is the total Chern class
`c(h^*ℰ)` of Stacks 0B7H. -/
theorem res_totalChernOfFiniteLocallyFree_of_rank {X' : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj F) s] :
    TotalChowClass.res h hs (totalChernOfFiniteLocallyFree C sX F) =
      totalChern C sX' ((Scheme.Modules.pullback h).obj F) s := by
  have hU := isClopenDecomposition_rankLociFamily F
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun r ↦ ?_
  have ha : ∀ r, h ⁻¹ᵁ rankLociFamily F r ≤ h ⁻¹ᵁ rankLociFamily F (id r) := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ rankLociFamily F r).ι ≫ h =
      pieceMap h (fun r ↦ h ⁻¹ᵁ rankLociFamily F r) (rankLociFamily F) id ha r ≫
        (rankLociFamily F r).ι :=
    (pieceMap_comp_ι h _ _ id ha r).symm
  have hpm : pieceMap h (fun r ↦ h ⁻¹ᵁ rankLociFamily F r) (rankLociFamily F) id ha r ≫
      ((rankLociFamily F r).ι ≫ sX) = (h ⁻¹ᵁ rankLociFamily F r).ι ≫ sX' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  let hpr := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down
    (pieceMap h (fun r ↦ h ⁻¹ᵁ rankLociFamily F r) (rankLociFamily F) id ha r)
  let hps := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback h).obj F) s (h ⁻¹ᵁ rankLociFamily F r).ι
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (rankLociFamily F r).ι rfl _ hpm,
    res_totalChernOfFiniteLocallyFree_rankLocus, TotalChowClass.res_totalChern,
    TotalChowClass.res_totalChern]
  let e := pullbackPullbackIsoOfComp hfac.symm F
  rcases isEmpty_or_nonempty (h ⁻¹ᵁ rankLociFamily F r : Scheme.{u}) with hE | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · have hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (h ⁻¹ᵁ rankLociFamily F r).ι).obj
          ((Scheme.Modules.pullback h).obj F)) r.down :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e hpr
    exact totalChern_congr C _ e (Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ hr hps y)

/-- **The operation of `c(ℰ)`** on a test scheme `g : T ⟶ X` along which `g^*ℰ` has constant
rank `s` is the total Chern class `c(g^*ℰ)` of the pulled back module, in the ring of graded cap
families: its index-`j` component is `c_j(g^*ℰ) ∩ -` for `j ≤ s`, and zero above. -/
theorem op_totalChernOfFiniteLocallyFree_of_rank {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj F) s] :
    (totalChernOfFiniteLocallyFree C sX F).op g =
      GenuineChern.chernFamily C (g ≫ sX) ((Scheme.Modules.pullback g).obj F) s := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback g).obj F) s (𝟙 T)
  refine eq_of_heq ((TotalChowClass.op_heq_congr _ (Category.id_comp g)).symm.trans
    ((TotalChowClass.op_res g rfl _ (𝟙 T)).symm.trans ?_))
  rw [res_totalChernOfFiniteLocallyFree_of_rank C sX F g rfl s, op_totalChern]
  exact GenuineChern.chernFamily_heq C (Category.id_comp _)
    ((Scheme.Modules.pullbackId T).app _) rfl

/-- **On a module of constant rank `r`**, `c(ℰ)` is the total Chern class
`1 + c_1(ℰ) + ⋯ + c_r(ℰ)` of Stacks 0B7H. -/
theorem totalChernOfFiniteLocallyFree_eq_totalChern (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    totalChernOfFiniteLocallyFree C sX F = totalChern C sX F r := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (𝟙 X)
  rw [← TotalChowClass.res_id (totalChernOfFiniteLocallyFree C sX F),
    res_totalChernOfFiniteLocallyFree_of_rank C sX F (𝟙 X) (Category.id_comp sX) r]
  exact totalChern_congr C sX ((Scheme.Modules.pullbackId X).app F) rfl

/-- **Restriction of `c(ℰ)`**: for every `h : X' ⟶ X` locally of finite type,
`res_h c(ℰ) = c(h^*ℰ)`, the pullback being again finite locally free. -/
theorem res_totalChernOfFiniteLocallyFree {X' : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') :
    haveI := isFiniteLocallyFree_pullbackObj F h
    TotalChowClass.res h hs (totalChernOfFiniteLocallyFree C sX F) =
      totalChernOfFiniteLocallyFree C sX' ((Scheme.Modules.pullback h).obj F) := by
  have hF' := isFiniteLocallyFree_pullbackObj F h
  have hU := isClopenDecomposition_rankLociFamily ((Scheme.Modules.pullback h).obj F)
  refine TotalChowClass.eq_of_res_eq hU fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily ((Scheme.Modules.pullback h).obj F) r
  let e := ((Scheme.Modules.pullbackComp
    (rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι h).app F).symm
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
        ((rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι ≫ h)).obj F) r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm ‹_›
  rw [TotalChowClass.res_res, res_totalChernOfFiniteLocallyFree_of_rank C sX F _ _ r.down,
    res_totalChernOfFiniteLocallyFree_rankLocus C sX' _ r]
  exact totalChern_congr C _ e rfl

/-- **Invariance of `c(ℰ)` under isomorphism.** -/
theorem totalChernOfFiniteLocallyFree_congr {F' : X.Modules}
    [hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F'] (e : F ≅ F') :
    totalChernOfFiniteLocallyFree C sX F = totalChernOfFiniteLocallyFree C sX F' := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily F) fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  let e' := (Scheme.Modules.pullback (rankLociFamily F r).ι).mapIso e
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F') r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e' ‹_›
  rw [res_totalChernOfFiniteLocallyFree_rankLocus C sX F r,
    res_totalChernOfFiniteLocallyFree_of_rank C sX F' _ _ r.down]
  exact totalChern_congr C _ e' rfl

/-- **`c(ℰ)` is a unit** of the ring of total classes: its inverse is glued from the inverses of
the `c(ℰ|_{X_r})`. -/
@[sga "7 XVII 5.3" "more general"]
theorem isUnit_totalChernOfFiniteLocallyFree : IsUnit (totalChernOfFiniteLocallyFree C sX F) := by
  have hU := isClopenDecomposition_rankLociFamily F
  let u : ∀ r : ULift.{u} ℕ, (TotalChowClass C ((rankLociFamily F r).ι ≫ sX))ˣ := fun r ↦
    let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
    totalChernUnit C _ ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down
  let d := TotalChowClass.glue hU fun r ↦ ((u r)⁻¹ : (TotalChowClass C _)ˣ).val
  have hres : ∀ r, TotalChowClass.res (rankLociFamily F r).ι rfl
      (totalChernOfFiniteLocallyFree C sX F) = (u r).val := fun r ↦ by
    exact res_totalChernOfFiniteLocallyFree_rankLocus C sX F r
  have h1 : totalChernOfFiniteLocallyFree C sX F * d = 1 :=
    TotalChowClass.eq_of_res_eq hU fun r ↦ by
      rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.mul_inv]
  have h2 : d * totalChernOfFiniteLocallyFree C sX F = 1 :=
    TotalChowClass.eq_of_res_eq hU fun r ↦ by
      rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.inv_mul]
  exact ⟨⟨_, d, h1, h2⟩, rfl⟩

/-! ### Two modules of arbitrary rank, and the Whitney sum formula -/

omit hF in
/-- **A total class is determined on the test schemes along which two given finite locally free
modules have constant rank**: the two decompositions of `X` by the ranks of `ℰ₁` and of `ℰ₂`
refine to one on whose pieces both ranks are constant, and Stacks 0FDZ applies twice. -/
theorem TotalChowClass.eq_of_res_eq_of_constantRank₂ (E₁ E₂ : X.Modules)
    [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
    [h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂]
    {a b : TotalChowClass C sX}
    (h : ∀ {T : Scheme.{u}} {sT : T ⟶ C.S} [LocallyOfFiniteType sT] (g : T ⟶ X)
      [LocallyOfFiniteType g] (hs : g ≫ sX = sT) (r s : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback g).obj E₁) r →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback g).obj E₂) s →
      TotalChowClass.res g hs a = TotalChowClass.res g hs b) : a = b := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E₁) fun r ↦ ?_
  have := isFiniteLocallyFree_pullbackObj E₂ (rankLociFamily E₁ r).ι
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily
    ((Scheme.Modules.pullback (rankLociFamily E₁ r).ι).obj E₂)) fun s ↦ ?_
  set ιs := (rankLociFamily ((Scheme.Modules.pullback (rankLociFamily E₁ r).ι).obj E₂) s).ι
  rw [TotalChowClass.res_res, TotalChowClass.res_res]
  refine h _ _ r.down s.down ?_ ?_
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp ιs (rankLociFamily E₁ r).ι).app E₁)
      (@pullbackPreservesRank_of_isFiniteLocallyFreeOfRank _ _ r.down
        (isFiniteLocallyFreeOfRank_pullback_rankLociFamily E₁ r) _ ιs)
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp ιs (rankLociFamily E₁ r).ι).app E₂)
      (isFiniteLocallyFreeOfRank_pullback_rankLociFamily _ s)

omit hF in
/-- **Stacks 02UI for modules of arbitrary rank.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of `𝒪_X`-modules with `ℰ₁`, `ℰ₂` finite locally free, of ranks that need
not be constant, `c(ℰ) = c(ℰ₁) c(ℰ₂)` for the total Chern classes of Stacks 0ESW. -/
theorem totalChernOfFiniteLocallyFree_eq_mul_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    haveI := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
    totalChernOfFiniteLocallyFree C sX S.X₂ =
      totalChernOfFiniteLocallyFree C sX S.X₁ * totalChernOfFiniteLocallyFree C sX S.X₃ := by
  have := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
  refine TotalChowClass.eq_of_res_eq_of_constantRank₂ C sX S.X₁ S.X₃
    fun {T sT _} g _ hs r s hr hs' ↦ ?_
  have hS' := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree g S hS
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₁ r := hr
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₃ s := hs'
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj S.X₂) (r + s) :=
    GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS' r s ‹_› ‹_›
  rw [map_mul, res_totalChernOfFiniteLocallyFree_of_rank C sX S.X₂ g hs (r + s),
    res_totalChernOfFiniteLocallyFree_of_rank C sX S.X₁ g hs r,
    res_totalChernOfFiniteLocallyFree_of_rank C sX S.X₃ g hs s]
  exact totalChern_eq_mul_of_shortExact C sT (S.map (Scheme.Modules.pullback g)) hS' r s

/-! ### Vanishing above the rank -/

/-- **`c_p(ℰ) = 0` above the rank.** If the rank of `ℰ` is less than `p` at every point, then
`c_p(ℰ) = 0`. -/
theorem totalChernOfFiniteLocallyFree_apply_eq_zero {p : ℕ} (hp : ∀ x : X, moduleRank F x < p) :
    totalChernOfFiniteLocallyFree C sX F p = 0 := by
  have hU := isClopenDecomposition_rankLociFamily F
  let d : TotalChowClass C sX := fun q ↦ if q = p then 0 else totalChernOfFiniteLocallyFree C sX F q
  have key : d = totalChernOfFiniteLocallyFree C sX F := TotalChowClass.eq_of_res_eq hU fun r ↦ by
    refine TotalChowClass.ext fun q ↦ ?_
    rw [TotalChowClass.res_rfl_apply, TotalChowClass.res_rfl_apply]
    by_cases hq : q = p
    · subst hq
      rw [show d q = 0 from if_pos rfl, map_zero, ← TotalChowClass.res_rfl_apply,
        res_totalChernOfFiniteLocallyFree_rankLocus]
      rcases isEmpty_or_nonempty (rankLociFamily F r : Scheme.{u}) with hE | ⟨⟨y⟩⟩
      · exact (congrArg (fun c : TotalChowClass C _ ↦ c q)
          ((TotalChowClass.subsingleton_of_isEmpty _).elim _ 0)).symm
      · have hy : moduleRank F y.1 = r.down := y.2
        let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
        exact (totalChern_apply_of_lt C _ _ r.down (hy ▸ hp y.1)).symm
    · rw [show d q = totalChernOfFiniteLocallyFree C sX F q from if_neg hq]
  exact (congrArg (fun c : TotalChowClass C sX ↦ c p) key).symm.trans (if_pos rfl)

end Stacks.Chow

end
