module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BoundedComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree

/-!
# The total Chern class of a locally bounded complex of finite locally free modules

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let `P`
be a locally bounded complex of finite locally free `𝒪_Y`-modules
(`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree`): near every point only finitely many terms are
nonzero. The rank function `n ↦ rank_x(P^n)` is then a finitely supported function of `n`
which is locally constant in `x`, so `Y` is the disjoint union of the open and closed rank loci

  `Y_ρ = {x ∈ Y : rank_x(P^n) = ρ(n) for all n}`,

and on `Y_ρ` the complex is bounded with constant ranks `ρ`. The total Chern class `c(P)` is the
total Chow cohomology class whose restriction to `Y_ρ` is `∏_n c(P^n|_{Y_ρ})^{(-1)^n}`, assembled
by [Stacks, Tag 0FDZ]. This is the class [Stacks, Tag 0FAF] and the section it belongs to work
with, for a perfect object represented by a locally bounded complex of finite locally free
modules.

## Main definitions

* `Stacks.Chow.complexRank` — the rank function of `P` at a point.
* `Stacks.Chow.complexRankLocus` — the rank locus `Y_ρ`.
* `Stacks.Chow.complexChern` — the total Chern class `c(P)`.

## Main results

* `Stacks.Chow.isClopenDecomposition_complexRankLoci` — `Y = ∐_ρ Y_ρ`.
* `Stacks.Chow.res_complexChern_complexRankLocus` — the restriction of `c(P)` to `Y_ρ` is the
  total Chern class of the bounded complex `P|_{Y_ρ}`.
* `Stacks.Chow.res_complexChern_eq_complexChernBounded` — more generally, the restriction of
  `c(P)` along any `h : Y' ⟶ Y` along which `h^*P` has constant ranks is `c(h^*P)` computed as a
  bounded complex.
* `Stacks.Chow.res_complexChern` — `res_h c(P) = c(h^*P)` for every `h : Y' ⟶ Y` locally of
  finite type.
* `Stacks.Chow.complexChern_eq_complexChernBounded` — on a bounded complex of constant ranks,
  `c(P) = ∏_n c(P^n)^{(-1)^n}`.
* `Stacks.Chow.complexChern_congr`, `Stacks.Chow.complexChern_congr_iso` — invariance under
  isomorphism.
* `Stacks.Chow.isUnit_complexChern` — `c(P)` is a unit.

## References

* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The rank function of a locally bounded complex -/

section Rank

variable {Y : Scheme.{u}}

/-- The fibre rank of a module vanishes at the points of an open subscheme to which it restricts
to zero. -/
theorem fiberRank_eq_zero_of_isZero_restrictModules (F : Y.Modules) (U : Y.Opens)
    (hF : IsZero ((RingedSpace.restrictModules Y.toRingedSpace U).obj F)) {x : Y} (hx : x ∈ U) :
    Scheme.Modules.fiberRank F x = 0 := by
  have h0 : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F) :=
    hF.of_iso ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y U).app
      F).symm
  exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι F ⟨x, hx⟩).symm.trans
    (Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _
      (subsingleton_moduleStalk_of_isZero h0 _))

variable {P : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)

include hP in
/-- The fibre ranks of the terms of a locally bounded complex of finite locally free modules are
locally constant. -/
theorem isLocallyConstant_fiberRank_X (n : ℤ) :
    IsLocallyConstant (Scheme.Modules.fiberRank (P.X n)) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
  rw [show Scheme.Modules.fiberRank (P.X n) = moduleRank (P.X n) from
    funext (fiberRank_eq_moduleRank (P.X n))]
  exact (moduleRank (P.X n)).isLocallyConstant

include hP in
/-- Near every point of `Y`, the terms of a locally bounded complex of finite locally free modules
outside a finite range of degrees have fibre rank zero. -/
theorem exists_fiberRank_X_eq_zero (x : Y) :
    ∃ U : Y.Opens, x ∈ U ∧ ∃ lo hi : ℤ, ∀ n : ℤ, (n < lo ∨ hi < n) → ∀ y ∈ U,
      Scheme.Modules.fiberRank (P.X n) y = 0 := by
  obtain ⟨U, hx, lo, hi, h⟩ := hP.2 x
  exact ⟨U, hx, lo, hi, fun n hn y hy ↦
    fiberRank_eq_zero_of_isZero_restrictModules _ U (h n hn) hy⟩

/-- **The rank function of a locally bounded complex at a point**: the finitely supported function
`n ↦ rank_x(P^n)`, the fibre rank at `x` of the `n`-th term. -/
def complexRank (x : Y) : ℤ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun n ↦ Scheme.Modules.fiberRank (P.X n) x) (by
    obtain ⟨U, hx, lo, hi, h⟩ := exists_fiberRank_X_eq_zero hP x
    refine (Set.finite_Icc lo hi).subset fun n hn ↦ ?_
    by_contra hn'
    rw [Set.mem_Icc] at hn'
    exact hn (h n (by omega) x hx))

/-- The value of the rank function at a degree is the fibre rank of the term in that degree. -/
theorem complexRank_apply (x : Y) (n : ℤ) :
    complexRank hP x n = Scheme.Modules.fiberRank (P.X n) x :=
  rfl

/-- **The rank locus `Y_ρ`** of a locally bounded complex: the open subscheme of the points at
which the rank function of the complex is `ρ`. It is open because near every point only finitely
many terms have nonzero rank and the rank of each term is locally constant. -/
def complexRankLocus (ρ : ℤ →₀ ℕ) : Y.Opens :=
  ⟨{x | complexRank hP x = ρ}, by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hxU, lo, hi, h⟩ := exists_fiberRank_X_eq_zero hP x
    refine ⟨(U : Set Y) ∩ ⋂ n ∈ Finset.Icc lo hi,
      {y | Scheme.Modules.fiberRank (P.X n) y = Scheme.Modules.fiberRank (P.X n) x}, ?_, ?_, ?_⟩
    · rintro y ⟨hyU, hy⟩
      refine Eq.trans (Finsupp.ext fun n ↦ ?_) hx
      rw [complexRank_apply, complexRank_apply]
      by_cases hn : n ∈ Finset.Icc lo hi
      · exact Set.mem_iInter₂.1 hy n hn
      · have hn' : n < lo ∨ hi < n := by
          rw [Finset.mem_Icc] at hn
          omega
        rw [h n hn' y hyU, h n hn' x hxU]
    · exact U.isOpen.inter (isOpen_biInter_finset fun n _ ↦
        (isLocallyConstant_fiberRank_X hP n).isOpen_fiber _)
    · exact ⟨hxU, Set.mem_iInter₂.2 fun n _ ↦ rfl⟩⟩

/-- A point lies in the rank locus `Y_ρ` exactly when the rank function there is `ρ`. -/
@[simp]
theorem mem_complexRankLocus {ρ : ℤ →₀ ℕ} {x : Y} :
    x ∈ complexRankLocus hP ρ ↔ complexRank hP x = ρ :=
  Iff.rfl

/-- The family of rank loci, indexed by `ULift (ℤ →₀ ℕ)` so that it lies in the universe of the
scheme, as Stacks 0FDZ requires. -/
abbrev complexRankLoci : ULift.{u} (ℤ →₀ ℕ) → Y.Opens := fun ρ ↦ complexRankLocus hP ρ.down

/-- **The decomposition `Y = ∐_ρ Y_ρ`** of the scheme into the rank loci of a locally bounded
complex of finite locally free modules: they are pairwise disjoint and cover `Y`. -/
theorem isClopenDecomposition_complexRankLoci : IsClopenDecomposition (complexRankLoci hP) where
  disjoint _ _ hij := Opens.coe_disjoint.mp <| Set.disjoint_left.mpr fun _ hx hy ↦
    hij (congrArg ULift.up
      (((mem_complexRankLocus hP).mp hx).symm.trans ((mem_complexRankLocus hP).mp hy)))
  iSup_eq_top := top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨ULift.up (complexRank hP x), rfl⟩

/-- On its rank locus `Y_ρ` the `n`-th term of the complex is finite locally free of rank
`ρ n`. -/
theorem isFiniteLocallyFreeOfRank_complexRankLocus (ρ : ℤ →₀ ℕ) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (complexRankLocus hP ρ).ι P).X n) (ρ n) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq (P.X n) _ (ρ n)
    fun x hx ↦ by rw [← complexRank_apply hP x n, (mem_complexRankLocus hP).mp hx]

end Rank

/-! ### The total Chern class -/

section Complex

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)

/-- **The total Chern class of a locally bounded complex of finite locally free modules.** On the
rank locus `Y_ρ` the complex is bounded with constant ranks `ρ`, and there the class is
`c(P|_{Y_ρ}) = ∏_n c(P^n|_{Y_ρ})^{(-1)^n}`; these classes are assembled into a total class on `Y`
by Stacks 0FDZ in every degree. -/
@[stacks 0ESZ "the class c(E^bullet) in prod_{p >= 0} A^p(Y) of a locally bounded complex of \
finite locally free modules -- the generalization the lemma refers to: no rank is assumed \
constant, the complex is only locally bounded, and Y is not assumed quasi-compact"]
def complexChern : TotalChowClass C sY :=
  TotalChowClass.glue (isClopenDecomposition_complexRankLoci hP) fun ρ ↦
    complexChernBounded C ((complexRankLoci hP ρ).ι ≫ sY)
      (pullbackComplex (complexRankLoci hP ρ).ι P) ρ.down
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down)

/-- **The restriction of `c(P)` to a rank locus** `Y_ρ` is the total Chern class of the bounded
complex `P|_{Y_ρ}` of constant ranks `ρ`. -/
theorem res_complexChern_complexRankLocus (ρ : ℤ →₀ ℕ) :
    TotalChowClass.res (complexRankLocus hP ρ).ι rfl (complexChern C sY hP) =
      complexChernBounded C ((complexRankLocus hP ρ).ι ≫ sY)
        (pullbackComplex (complexRankLocus hP ρ).ι P) ρ
        (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ) :=
  TotalChowClass.res_glue (isClopenDecomposition_complexRankLoci hP) _ (ULift.up ρ)

/-- Pulling back along `f` and then along `g` agrees, termwise, with pulling back along any
morphism equal to `g ≫ f`, and with pulling back along `g'` and then `f'` when
`g ≫ f = g' ≫ f'`. -/
def pullbackPullbackIsoOfComp {A B D E : Scheme.{u}} {f : B ⟶ D} {g : A ⟶ B} {f' : E ⟶ D}
    {g' : A ⟶ E} (e : g ≫ f = g' ≫ f') (F : D.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj F) ≅
      (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f').obj F) :=
  (Scheme.Modules.pullbackComp g f).app F ≪≫ (Scheme.Modules.pullbackCongr e).app F ≪≫
    ((Scheme.Modules.pullbackComp g' f').app F).symm

/-- **Characterization of `c(P)`.** For every `h : Y' ⟶ Y` locally of finite type along which
the termwise pullback `h^*P` has constant ranks `σ`, the restriction of `c(P)` along `h` is the
total Chern class `∏_n c(h^*P^n)^{(-1)^n}` of the bounded complex `h^*P`. -/
theorem res_complexChern_eq_complexChernBounded {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h P).X n) (σ n)) :
    TotalChowClass.res h hs (complexChern C sY hP) =
      complexChernBounded C sY' (pullbackComplex h P) σ hσ := by
  have hU := isClopenDecomposition_complexRankLoci hP
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun ρ ↦ ?_
  have ha : ∀ ρ, h ⁻¹ᵁ complexRankLoci hP ρ ≤ h ⁻¹ᵁ complexRankLoci hP (id ρ) := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ complexRankLoci hP ρ).ι ≫ h =
      pieceMap h (fun ρ ↦ h ⁻¹ᵁ complexRankLoci hP ρ) (complexRankLoci hP) id ha ρ ≫
        (complexRankLoci hP ρ).ι :=
    (pieceMap_comp_ι h _ _ id ha ρ).symm
  have hpm : pieceMap h (fun ρ ↦ h ⁻¹ᵁ complexRankLoci hP ρ) (complexRankLoci hP) id ha ρ ≫
      ((complexRankLoci hP ρ).ι ≫ sY) = (h ⁻¹ᵁ complexRankLoci hP ρ).ι ≫ sY' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (complexRankLoci hP ρ).ι rfl _ hpm,
    complexChern, TotalChowClass.res_glue hU, TotalChowClass.res_complexChernBounded,
    TotalChowClass.res_complexChernBounded]
  exact complexChernBounded_congr C _ _
    (fun n ↦ pullbackPullbackIsoOfComp hfac.symm (P.X n)) _ _ _ _

/-- If the termwise pullback `h^*P` is isomorphic termwise to a complex `Q` of constant ranks `ρ`,
then the restriction of `c(P)` along `h` is `c(Q)` computed as a bounded complex. -/
private theorem res_complexChern_eq_of_iso {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (ρ : ℤ →₀ ℕ) {Q : CochainComplex Y'.Modules ℤ} (e : ∀ n, (pullbackComplex h P).X n ≅ Q.X n)
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n)
      (ρ n)) :
    TotalChowClass.res h hs (complexChern C sY hP) = complexChernBounded C sY' Q ρ hQ := by
  rw [res_complexChern_eq_complexChernBounded C sY hP h hs ρ fun n ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e n).symm (hQ n)]
  exact complexChernBounded_congr C _ _ e _ _ _ _

/-- **`c(P)` of a bounded complex of constant ranks** is `∏_n c(P^n)^{(-1)^n}`: the locally
bounded construction extends the bounded one. -/
theorem complexChern_eq_complexChernBounded (ρ : ℤ →₀ ℕ)
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n)
      (ρ n)) :
    complexChern C sY hP = complexChernBounded C sY P ρ hρ := by
  rw [← TotalChowClass.res_id (complexChern C sY hP),
    res_complexChern_eq_complexChernBounded C sY hP (𝟙 Y) (Category.id_comp sY) ρ
      (isFiniteLocallyFreeOfRank_pullbackComplex_X P (𝟙 Y) ρ hρ)]
  exact complexChernBounded_congr C sY _
    (fun n ↦ (Scheme.Modules.pullbackId Y).app (P.X n)) _ _ _ _

/-- **Restriction of `c(P)`**: for every `h : Y' ⟶ Y` locally of finite type, the restriction of
`c(P)` along `h` is the total Chern class of the termwise pullback `h^*P`, which is again a
locally bounded complex of finite locally free modules. -/
theorem res_complexChern {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') :
    TotalChowClass.res h hs (complexChern C sY hP) =
      complexChern C sY'
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP) := by
  set hP' := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP') fun ρ ↦ ?_
  rw [TotalChowClass.res_res,
    res_complexChern_eq_of_iso C sY hP ((complexRankLoci hP' ρ).ι ≫ h) _ ρ.down
      (Q := pullbackComplex (complexRankLoci hP' ρ).ι (pullbackComplex h P))
      (fun n ↦ ((Scheme.Modules.pullbackComp (complexRankLoci hP' ρ).ι h).app (P.X n)).symm)
      (isFiniteLocallyFreeOfRank_complexRankLocus hP' ρ.down),
    res_complexChern_complexRankLocus C sY' hP' ρ.down]

/-- **Invariance of `c(P)` under isomorphism**: locally bounded complexes of finite locally free
modules with isomorphic terms have the same total Chern class. -/
theorem complexChern_congr {P' : CochainComplex Y.Modules ℤ}
    (hP' : IsLocallyBoundedFiniteLocallyFree P') (e : ∀ n, P.X n ≅ P'.X n) :
    complexChern C sY hP = complexChern C sY hP' := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [res_complexChern_complexRankLocus C sY hP ρ.down,
    res_complexChern_eq_of_iso C sY hP' (complexRankLoci hP ρ).ι rfl ρ.down
      (Q := pullbackComplex (complexRankLoci hP ρ).ι P)
      (fun n ↦ ((Scheme.Modules.pullback (complexRankLoci hP ρ).ι).mapIso (e n)).symm)
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down)]

/-- **Invariance of `c(P)` under isomorphism of complexes.** -/
theorem complexChern_congr_iso {P' : CochainComplex Y.Modules ℤ}
    (hP' : IsLocallyBoundedFiniteLocallyFree P') (e : P ≅ P') :
    complexChern C sY hP = complexChern C sY hP' :=
  complexChern_congr C sY hP hP' fun n ↦ (HomologicalComplex.eval _ _ n).mapIso e

/-- **`c(P)` is a unit** of the ring of total classes: its inverse is glued from the inverses of
the total Chern classes of the bounded complexes `P|_{Y_ρ}`. -/
theorem isUnit_complexChern : IsUnit (complexChern C sY hP) := by
  have hU := isClopenDecomposition_complexRankLoci hP
  let u : ∀ ρ, (TotalChowClass C ((complexRankLoci hP ρ).ι ≫ sY))ˣ := fun ρ ↦
    complexChernProd C _ (pullbackComplex (complexRankLoci hP ρ).ι P) ρ.down
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down) ρ.down.support
  let d := TotalChowClass.glue hU fun ρ ↦ ((u ρ)⁻¹ : (TotalChowClass C _)ˣ).val
  have hres : ∀ ρ, TotalChowClass.res (complexRankLoci hP ρ).ι rfl (complexChern C sY hP) =
      (u ρ).val := fun ρ ↦ by rw [complexChern, TotalChowClass.res_glue hU]; rfl
  have h1 : complexChern C sY hP * d = 1 := TotalChowClass.eq_of_res_eq hU fun ρ ↦ by
    rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.mul_inv]
  have h2 : d * complexChern C sY hP = 1 := TotalChowClass.eq_of_res_eq hU fun ρ ↦ by
    rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.inv_mul]
  exact ⟨⟨_, d, h1, h2⟩, rfl⟩

end Complex

end Stacks.Chow

end
