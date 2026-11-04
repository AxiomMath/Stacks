module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.FirstPageConnecting
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESDefect
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# A cochain acting on a filtered complex, and the first differential

Let `(K, F)` be a filtered complex of an abelian category `𝒞`, `Φ : 𝒞 ⥤ 𝒟` an exact functor and
`w` a cochain of degree `p` on `Φ(K)` which carries `Φ(F^kK)` into `Φ(F^{k+p}K)` for every `k`
(`CochainComplex.Filtered.RespectsFiltration`). If its coboundary `δw`, a cochain of degree
`p + 1`, carries `Φ(F^kK)` into `Φ(F^{k+p+1}K)`, then `w` induces morphisms of complexes

`μ_w^k : Φ(gr^kK) ⟶ Φ(gr^{k+p}K)[p]`

on the graded pieces (`CochainComplex.Filtered.actionGr`), although it is in general not a
morphism of complexes on `Φ(K)` itself: its failure to be one is `δw`, which raises the filtration
by one more step and so dies on the graded pieces.

This is the situation of the Katz–Oda description of the Gauss–Manin connection in
[Stacks, Tag 0FMN]: `K` is the de Rham complex `Ω^•_{X/S}` filtered by the forms pulled back from
`Y`, `Φ` is restriction to an open `f⁻¹(U)`, and `w` is wedge multiplication by the pull back of
a `p`-form `ω` on `U`, whose coboundary is wedge multiplication by the pull back of `dω`.

The middle term `F^k/F^{k+2}` of the graded short exact sequence
`0 ⟶ gr^{k+1} ⟶ F^k/F^{k+2} ⟶ gr^k ⟶ 0` only receives a degree-zero cochain
(`CochainComplex.Filtered.actionMid`), whose defect is `δw`: this is the input of the Leibniz rule
`DerivedCategory.map_triangleOfSESδ_of_defect` for the connecting morphisms.

## Main definitions

* `CochainComplex.Filtered.RespectsFiltration`: the cochain `w` carries `Φ(F^k)` into
  `Φ(F^{k+p})`.
* `CochainComplex.Filtered.actionStep`: the induced morphism `Φ(F^kK^n) ⟶ Φ(F^{k+p}K^{n+p})`.
* `CochainComplex.Filtered.actionGr`: **the morphism of complexes
  `μ_w^k : Φ(gr^kK) ⟶ Φ(gr^{k+p}K)[p]`.**
* `CochainComplex.Filtered.actionMid`: the degree-zero cochain
  `Φ(F^k/F^{k+2}) ⟶ Φ(F^{k'}/F^{k'+2})[p]` induced by `w`, and `actionDefect` its defect.
* `CochainComplex.Filtered.derivedConnecting` and `CochainComplex.Filtered.derivedShiftedMap`:
  the connecting morphisms and the actions after a functor of derived categories.

## Main results

* `CochainComplex.Filtered.grπ_actionGr`: `μ_w^k` is characterized by `π ∘ μ_w^k = π ∘ w` on
  `Φ(F^k)`.
* `CochainComplex.Filtered.actionStep_d`: on `Φ(F^k)` the action commutes with the differentials
  up to `(-1)^p` and `δw`.
* `CochainComplex.Filtered.Q_map_actionGr_comp_triangleOfSESδ`: **the Leibniz rule of the
  connecting morphisms in the derived category**,
  `μ_w^k ≫ δ_{k'}[p] = δ_k ≫ μ_w^{k+1}[1] + (-1)^p μ_{δw}^k`.
* `CochainComplex.Filtered.derivedShiftedMap_actionGr_comp_derivedConnecting`: the same after a
  functor `G` of derived categories commuting with the shifts, with the connecting morphism of
  the unshifted sequence.
* `CochainComplex.Filtered.shiftMap_actionGr_comp_derivedConnecting`: **the Leibniz rule on
  cohomology**, `d ∘ μ_w^k = μ_{δw}^k + (-1)^p μ_w^{k+1} ∘ d`.
* `CategoryTheory.Functor.shiftMap_comp_shiftMap`: maps induced on a shift sequence compose.
* `CochainComplex.Filtered.mapDerivedCategory_map_triangleOfSESδ`: `Φ` on derived categories
  carries the graded connecting morphism of `K` to the one of `Φ(K)`.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite Preadditive CochainComplex.HomComplex

namespace CochainComplex.Filtered

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (M : Filtered C)

/-- The inclusion `F^kK^n ⟶ K^n`. -/
abbrev stepι (k n : ℤ) : (M.filtration.obj (op k)).X n ⟶ M.X.X n :=
  (M.filtration.ι.app (op k)).f n

/-- The inclusion `F^kK^n ⟶ K^n` is a monomorphism. -/
instance (k n : ℤ) : Mono (M.stepι k n) :=
  inferInstanceAs (Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
    (M.filtration.ι.app (op k))))

/-- **A cochain of degree `p` on `Φ(K)` respects the filtration** if it carries `Φ(F^kK)` into
`Φ(F^{k'}K)` whenever `k + p = k'`: in each degree, `Φ(F^kK^n) ⟶ Φ(K^n) ⟶ Φ(K^m)` dies in the
cokernel of `Φ(F^{k'}K^m) ⟶ Φ(K^m)`. -/
def RespectsFiltration {p : ℤ}
    (w : Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X) p) : Prop :=
  ∀ (k k' : ℤ) (_ : k + p = k') (n m : ℤ) (h : n + p = m),
    F.map (M.stepι k n) ≫ w.v n m h ≫ F.map (cokernel.π (M.stepι k' m)) = 0

variable {F M} {p : ℤ}
  {w : Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X) p}

/-- The short exact sequence `0 ⟶ F^kK^m ⟶ K^m ⟶ cokernel ⟶ 0`, after `Φ`. -/
lemma exact_map_stepι (k m : ℤ) :
    ((ShortComplex.mk (M.stepι k m) (cokernel.π (M.stepι k m)) (cokernel.condition _)).map
      F).Exact :=
  (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)).map F

/-- After `Φ`, the inclusion `F^kK^m ⟶ K^m` is a monomorphism. -/
instance (k m : ℤ) : Mono ((ShortComplex.mk (M.stepι k m) (cokernel.π (M.stepι k m))
    (cokernel.condition _)).map F).f :=
  inferInstanceAs (Mono (F.map (M.stepι k m)))

/-- **The morphism `Φ(F^kK^n) ⟶ Φ(F^{k'}K^m)` induced by a cochain respecting the
filtration.** -/
def actionStep (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') (n m : ℤ)
    (h : n + p = m) :
    F.obj ((M.filtration.obj (op k)).X n) ⟶ F.obj ((M.filtration.obj (op k')).X m) :=
  (exact_map_stepι (F := F) (M := M) k' m).lift (F.map (M.stepι k n) ≫ w.v n m h)
    (by simpa using hw k k' hk n m h)

/-- `actionStep` followed by the inclusion `Φ(F^{k'}K^m) ⟶ Φ(K^m)` is `w` on `Φ(F^kK^n)`. -/
@[reassoc (attr := simp)]
lemma actionStep_ι (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') (n m : ℤ)
    (h : n + p = m) :
    actionStep hw k k' hk n m h ≫ F.map (M.stepι k' m) = F.map (M.stepι k n) ≫ w.v n m h :=
  (exact_map_stepι (F := F) (M := M) k' m).lift_f _ _

/-- `actionStep` commutes with the inclusions between the steps of the filtration. -/
@[reassoc]
lemma map_comp_actionStep (hw : RespectsFiltration F M w) {a b a' b' : ℤ} (ha : a + p = a')
    (hb : b + p = b') (t : M.filtration.obj (op a) ⟶ M.filtration.obj (op b))
    (t' : M.filtration.obj (op a') ⟶ M.filtration.obj (op b'))
    (ht : t ≫ M.filtration.ι.app (op b) = M.filtration.ι.app (op a))
    (ht' : t' ≫ M.filtration.ι.app (op b') = M.filtration.ι.app (op a')) (n m : ℤ)
    (h : n + p = m) :
    F.map (t.f n) ≫ actionStep hw b b' hb n m h = actionStep hw a a' ha n m h ≫ F.map (t'.f m) := by
  rw [← cancel_mono (F.map (M.stepι b' m)), assoc, assoc, actionStep_ι, ← F.map_comp,
    ← HomologicalComplex.comp_f, ht', actionStep_ι, ← F.map_comp_assoc,
    ← HomologicalComplex.comp_f, ht]

/-! ### Descending along a cokernel of complexes, degreewise and after `Φ` -/

section Quot

variable (F) {K L : CochainComplex C ℤ} (s : K ⟶ L) (n : ℤ)

/-- After `Φ`, the degree-`n` component of the projection onto the cokernel of a morphism of
complexes is a cokernel of the degree-`n` component of that morphism. -/
def quotIsColimit :
    IsColimit (CokernelCofork.ofπ (F.map ((cokernel.π s).f n))
      (by rw [← F.map_comp, ← HomologicalComplex.comp_f, cokernel.condition,
        HomologicalComplex.zero_f, F.map_zero]) : CokernelCofork (F.map (s.f n))) :=
  CokernelCofork.mapIsColimit _ (cokernelIsCokernel s)
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n ⋙ F)

/-- Descending a morphism out of `Φ(L^n)` along `Φ(L^n) ⟶ Φ(cokernel(s)^n)`. -/
def quotDesc {Z : D} (t : F.obj (L.X n) ⟶ Z) (ht : F.map (s.f n) ≫ t = 0) :
    F.obj ((cokernel s).X n) ⟶ Z :=
  (quotIsColimit F s n).desc (CokernelCofork.ofπ t ht)

omit [PreservesFiniteLimits F] in
/-- Precomposed with `Φ(L^n) ⟶ Φ(cokernel(s)^n)`, `quotDesc` is the morphism it descends. -/
@[reassoc (attr := simp)]
lemma map_π_quotDesc {Z : D} (t : F.obj (L.X n) ⟶ Z) (ht : F.map (s.f n) ≫ t = 0) :
    F.map ((cokernel.π s).f n) ≫ quotDesc F s n t ht = t :=
  (quotIsColimit F s n).fac _ WalkingParallelPair.one

/-- After `Φ`, the degree-`n` component of the projection onto the cokernel of a morphism of
complexes is an epimorphism. -/
instance : Epi (F.map ((cokernel.π s).f n)) :=
  epi_of_isColimit_cofork (quotIsColimit F s n)

end Quot

/-! ### The morphisms on the graded pieces -/

/-- The inclusion of the step `F^{k+1}` into `F^k` composed with the inclusion of `F^k` is the
inclusion of `F^{k+1}`. -/
@[reassoc (attr := simp)]
lemma succStep_ι (k : ℤ) :
    M.succStep k ≫ M.filtration.ι.app (op k) = M.filtration.ι.app (op (k + 1)) :=
  Filtration.step_comp_ι_app _ _

/-- The projection of `actionStep` onto `Φ(gr^{k'})` vanishes on `Φ(F^{k+1})`. -/
lemma map_succStep_actionStep_grπ (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k')
    (n m : ℤ) (h : n + p = m) :
    F.map ((M.succStep k).f n) ≫ actionStep hw k k' hk n m h ≫ F.map ((M.grπ k').f m) = 0 := by
  rw [map_comp_actionStep_assoc hw (a' := k' + 1) (by omega) hk _ (M.succStep k')
    (succStep_ι (M := M) k) (succStep_ι (M := M) k'), ← F.map_comp, succStep_f_grπ_f,
    F.map_zero, comp_zero]

/-- The degree-`n` component of `μ_w^k`. -/
def actionGrF (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') (n m : ℤ)
    (h : n + p = m) :
    F.obj (((FilteredObject.gr k).obj M).X n) ⟶ F.obj (((FilteredObject.gr k').obj M).X m) :=
  quotDesc F (M.succStep k) n (actionStep hw k k' hk n m h ≫ F.map ((M.grπ k').f m))
    (map_succStep_actionStep_grπ hw k k' hk n m h)

/-- Precomposed with the projection `Φ(F^kK^n) ⟶ Φ(gr^kK^n)`, `actionGrF` is `actionStep`
followed by the projection `Φ(F^{k'}K^m) ⟶ Φ(gr^{k'}K^m)`. -/
@[reassoc (attr := simp)]
lemma grπ_actionGrF (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') (n m : ℤ)
    (h : n + p = m) :
    F.map ((M.grπ k).f n) ≫ actionGrF hw k k' hk n m h =
      actionStep hw k k' hk n m h ≫ F.map ((M.grπ k').f m) :=
  map_π_quotDesc F (M.succStep k) n _ _

/-- After `Φ`, the projection `F^kK^n ⟶ gr^kK^n` is an epimorphism. -/
instance (k n : ℤ) : Epi (F.map ((M.grπ k).f n)) :=
  inferInstanceAs (Epi (F.map ((cokernel.π (M.succStep k)).f n)))

/-- A functor carries a morphism of complexes to a family commuting with the differentials. -/
private lemma map_f_comp_map_d {E : Type*} [Category* E] (G : C ⥤ E) {K L : CochainComplex C ℤ}
    (s : K ⟶ L) (a b : ℤ) : G.map (s.f a) ≫ G.map (L.d a b) = G.map (K.d a b) ≫ G.map (s.f b) := by
  rw [← G.map_comp, ← G.map_comp, s.comm]

/-- On `Φ(F^k)`, the action commutes with the differentials up to the sign `(-1)^p` and the
coboundary `δw`, which raises the filtration by `p + 1`. -/
lemma actionStep_d (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k')
    (n m n₁ m₁ : ℤ) (h : n + p = m) (h₁ : n₁ + p = m₁) (hn : n + 1 = n₁) :
    p.negOnePow • (actionStep hw k k' hk n m h ≫
        F.map ((M.filtration.obj (op k')).d m m₁)) -
      F.map ((M.filtration.obj (op k)).d n n₁) ≫ actionStep hw k k' hk n₁ m₁ h₁ =
      p.negOnePow • (actionStep hw' k (k' + 1) (by omega) n m₁ (by omega) ≫
        F.map ((M.succStep k').f m₁)) := by
  have hd : ∀ (j : ℤ) (a b : ℤ), F.map ((M.filtration.obj (op j)).d a b) ≫ F.map (M.stepι j b) =
      F.map (M.stepι j a) ≫ F.map (M.X.d a b) := fun j a b =>
    (map_f_comp_map_d F (M.filtration.ι.app (op j)) a b).symm
  have hs : F.map ((M.succStep k').f m₁) ≫ F.map (M.stepι k' m₁) =
      F.map (M.stepι (k' + 1) m₁) := by
    rw [← F.map_comp, ← HomologicalComplex.comp_f, succStep_ι]
  rw [← cancel_mono (F.map (M.stepι k' m₁))]
  simp only [sub_comp, Linear.units_smul_comp, assoc, actionStep_ι, hs, hd, actionStep_ι_assoc]
  rw [← assoc (F.map ((M.filtration.obj (op k)).d n n₁)), hd, assoc]
  rw [δ_v p (p + 1) rfl w n m₁ (by omega) m n₁ (by omega) hn]
  subst hn h h₁
  simp only [comp_add, Linear.comp_units_smul, smul_add, smul_smul, Int.negOnePow_succ,
    Int.units_mul_self, one_smul, sub_eq_add_neg, Units.neg_smul,
    comp_neg, smul_neg, Functor.mapHomologicalComplex_obj_d]

/-- **The morphism of complexes `μ_w^k : Φ(gr^kK) ⟶ Φ(gr^{k'}K)[p]`**, `k + p = k'`, induced on the
graded pieces by a cochain `w` of degree `p` respecting the filtration whose coboundary respects
the filtration with one more step. In degree `n` it is `π ∘ w` on `Φ(F^kK^n)`, descended to
`Φ(gr^kK^n)` (`grπ_actionGr`). -/
def actionGr (hw : RespectsFiltration F M w) (hw' : RespectsFiltration F M (δ p (p + 1) w))
    (k k' : ℤ) (hk : k + p = k') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k).obj M) ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k').obj M))⟦p⟧ where
  f n := actionGrF hw k k' hk n (n + p) rfl
  comm' i j hij := by
    have hij : i + 1 = j := hij
    rw [← cancel_epi (F.map ((M.grπ k).f i)), ← sub_eq_zero]
    have hd := actionStep_d hw hw' k k' hk i (i + p) j (j + p) rfl rfl hij
    have hπ : ∀ (l a b : ℤ), F.map ((M.grπ l).f a) ≫ F.map (((FilteredObject.gr l).obj M).d a b) =
        F.map ((M.filtration.obj (op l)).d a b) ≫ F.map ((M.grπ l).f b) := fun l a b => by
      rw [← F.map_comp, ← F.map_comp, (M.grπ l).comm]
    have key : F.map ((M.grπ k).f i) ≫ actionGrF hw k k' hk i (i + p) rfl ≫
          (p.negOnePow • F.map (((FilteredObject.gr k').obj M).d (i + p) (j + p))) -
        F.map ((M.grπ k).f i) ≫ F.map (((FilteredObject.gr k).obj M).d i j) ≫
          actionGrF hw k k' hk j (j + p) rfl =
        (p.negOnePow • (actionStep hw k k' hk i (i + p) rfl ≫
          F.map ((M.filtration.obj (op k')).d (i + p) (j + p))) -
        F.map ((M.filtration.obj (op k)).d i j) ≫ actionStep hw k k' hk j (j + p) rfl) ≫
          F.map ((M.grπ k').f (j + p)) := by
      simp only [Linear.comp_units_smul, grπ_actionGrF_assoc, hπ, sub_comp,
        Linear.units_smul_comp, assoc]
      rw [← assoc (F.map ((M.grπ k).f i)), hπ, assoc, grπ_actionGrF]
    refine key.trans ?_
    rw [hd, Linear.units_smul_comp, assoc, ← F.map_comp, succStep_f_grπ_f, F.map_zero,
      comp_zero, smul_zero]

/-- `μ_w^k` is characterized by `π ∘ μ_w^k = π ∘ w` on `Φ(F^kK^n)`. -/
@[reassoc (attr := simp)]
lemma grπ_actionGr (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') (n : ℤ) :
    F.map ((M.grπ k).f n) ≫ (actionGr hw hw' k k' hk).f n =
      actionStep hw k k' hk n (n + p) rfl ≫ F.map ((M.grπ k').f (n + p)) :=
  grπ_actionGrF hw k k' hk n (n + p) rfl

/-- The degree-`n` component of `μ_w^k` does not depend on how the target degree is named. -/
lemma actionGrF_XIsoOfEq (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k')
    (n m m' : ℤ) (h : n + p = m) (hm : m = m') :
    actionGrF hw k k' hk n m h ≫ F.map ((((FilteredObject.gr k').obj M).XIsoOfEq hm).hom) =
      actionGrF hw k k' hk n m' (h.trans hm) := by
  subst hm
  simp

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The coboundary of the coboundary vanishes, so it respects the filtration. -/
lemma respectsFiltration_δ_δ :
    RespectsFiltration F M (δ (p + 1) (p + 1 + 1) (δ p (p + 1) w)) := by
  intro k k' _ n m h
  rw [δ_δ, Cochain.zero_v, zero_comp, comp_zero]

/-! ### The graded short exact sequences, after `Φ` -/

variable (F M) in
/-- `0 ⟶ Φ(gr^{k+1}) ⟶ Φ(F^k/F^{k+2}) ⟶ Φ(gr^k) ⟶ 0`. -/
abbrev grShortComplexFunctorMap (k : ℤ) : ShortComplex (CochainComplex D ℤ) :=
  (M.grShortComplex k).map (F.mapHomologicalComplex (ComplexShape.up ℤ))

variable (F M) in
/-- The sequence `0 ⟶ Φ(gr^{k+1}) ⟶ Φ(F^k/F^{k+2}) ⟶ Φ(gr^k) ⟶ 0` is short exact. -/
lemma grShortComplexFunctorMap_shortExact (k : ℤ) : (grShortComplexFunctorMap F M k).ShortExact :=
  (M.grShortComplex_shortExact k).map_of_exact _

/-- The middle map: `w` on `Φ(F^k/F^{k+2}) ⟶ Φ(F^{k'}/F^{k'+2})[p]`, a cochain of degree `0`. -/
def actionMid (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') :
    Cochain (grShortComplexFunctorMap F M k).X₂
      ((grShortComplexFunctorMap F M k').X₂⟦p⟧) 0 :=
  Cochain.ofHoms fun n =>
    quotDesc F (M.succStep (k + 1) ≫ M.succStep k) n
      (actionStep hw k k' hk n (n + p) rfl ≫
        F.map ((cokernel.π (M.succStep (k' + 1) ≫ M.succStep k')).f (n + p))) (by
      rw [map_comp_actionStep_assoc hw (a' := k' + 1 + 1) (by omega) hk _
          (M.succStep (k' + 1) ≫ M.succStep k') (by simp) (by simp), ← F.map_comp,
        ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, F.map_zero,
        comp_zero])

/-- Precomposed with the projection `Φ(F^kK^n) ⟶ Φ((F^k/F^{k+2})^n)`, `actionMid` is
`actionStep` followed by the projection `Φ(F^{k'}K^{n+p}) ⟶ Φ((F^{k'}/F^{k'+2})^{n+p})`. -/
@[reassoc]
lemma π_actionMid_v (hw : RespectsFiltration F M w) (k k' : ℤ) (hk : k + p = k') (n : ℤ) :
    F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n) ≫
        (actionMid hw k k' hk).v n n (add_zero n) =
      actionStep hw k k' hk n (n + p) rfl ≫
        F.map ((cokernel.π (M.succStep (k' + 1) ≫ M.succStep k')).f (n + p)) := by
  rw [actionMid, Cochain.ofHoms_v]
  exact map_π_quotDesc F _ n _ _

variable (M) in
/-- The first map of the graded short exact sequence, on the projections. -/
@[reassoc]
lemma grπ_grShortComplex_f (k : ℤ) :
    M.grπ (k + 1) ≫ (M.grShortComplex k).f =
      M.succStep k ≫ cokernel.π (M.succStep (k + 1) ≫ M.succStep k) := by
  simp [FilteredObject.grMapπ, cokernel.map]

variable (M) in
/-- The second map of the graded short exact sequence, on the projections. -/
@[reassoc]
lemma π_grShortComplex_g (k : ℤ) :
    cokernel.π (M.succStep (k + 1) ≫ M.succStep k) ≫ (M.grShortComplex k).g = M.grπ k := by
  simp [FilteredObject.grMapπ, cokernel.map]

/-- The first compatibility of `actionMid` with the actions on the graded pieces. -/
lemma ofHom_f_comp_actionMid (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    (Cochain.ofHom (grShortComplexFunctorMap F M k).f).comp (actionMid hw k k' hk) (zero_add 0) =
      Cochain.ofHom (actionGr hw hw' (k + 1) (k' + 1) (by omega) ≫
        ((grShortComplexFunctorMap F M k').f)⟦p⟧') := by
  ext n
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v,
    ← cancel_epi (F.map ((M.grπ (k + 1)).f n))]
  show F.map ((M.grπ (k + 1)).f n) ≫ F.map ((M.grShortComplex k).f.f n) ≫ _ =
    F.map ((M.grπ (k + 1)).f n) ≫ (actionGr hw hw' (k + 1) (k' + 1) _).f n ≫
      F.map ((M.grShortComplex k').f.f (n + p))
  rw [← F.map_comp_assoc, ← HomologicalComplex.comp_f, grπ_grShortComplex_f,
    HomologicalComplex.comp_f, F.map_comp, assoc, π_actionMid_v, grπ_actionGr_assoc,
    ← F.map_comp, ← HomologicalComplex.comp_f, grπ_grShortComplex_f, HomologicalComplex.comp_f,
    F.map_comp, map_comp_actionStep_assoc hw (a' := k' + 1) (by omega) hk _ (M.succStep k')
      (succStep_ι (M := M) k) (succStep_ι (M := M) k')]

/-- The second compatibility of `actionMid` with the actions on the graded pieces. -/
lemma actionMid_comp_ofHom_g (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    (actionMid hw k k' hk).comp (Cochain.ofHom ((grShortComplexFunctorMap F M k').g⟦p⟧'))
      (zero_add 0) =
      Cochain.ofHom ((grShortComplexFunctorMap F M k).g ≫ actionGr hw hw' k k' hk) := by
  ext n
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v,
    ← cancel_epi (F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n))]
  show _ ≫ _ ≫ F.map ((M.grShortComplex k').g.f (n + p)) =
    F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n) ≫
      F.map ((M.grShortComplex k).g.f n) ≫ (actionGr hw hw' k k' hk).f n
  rw [reassoc_of% (π_actionMid_v hw k k' hk n), ← F.map_comp, ← HomologicalComplex.comp_f,
    π_grShortComplex_g, ← F.map_comp_assoc, ← HomologicalComplex.comp_f, π_grShortComplex_g,
    grπ_actionGr]

/-- `actionGr` after the identification of two names for the target degree. -/
@[reassoc]
lemma grπ_actionGr_XIsoOfEq (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') (n m : ℤ)
    (hm : n + p = m) :
    F.map ((M.grπ k).f n) ≫ (actionGr hw hw' k k' hk).f n ≫
        F.map ((((FilteredObject.gr k').obj M).XIsoOfEq hm).hom) =
      actionStep hw k k' hk n m hm ≫ F.map ((M.grπ k').f m) := by
  subst hm
  simp

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- For `a = b`, the identification `Φ(K)^a ≅ Φ(K)^b` is `Φ` of the identification `K^a ≅ K^b`. -/
lemma mapHomologicalComplex_XIsoOfEq_hom (K : CochainComplex C ℤ) {a b : ℤ} (h : a = b) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).XIsoOfEq h).hom =
      F.map ((K.XIsoOfEq h).hom) := by
  subst h
  simp

/-- The defect of `actionMid`: wedge with `δw`, read as a morphism of complexes
`Φ(gr^k) ⟶ Φ(gr^{k'+1})[p][1]`, up to the sign `(-1)^p`. -/
def actionDefect (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k).obj M) ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((FilteredObject.gr (k' + 1)).obj M))⟦p⟧⟦(1 : ℤ)⟧ :=
  p.negOnePow • (actionGr hw' respectsFiltration_δ_δ k (k' + 1) (by omega) ≫
    (CategoryTheory.shiftFunctorAdd' (CochainComplex D ℤ) p 1 (p + 1) rfl).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr (k' + 1)).obj M)))

/-- **The defect of the middle map**: `δ(actionMid) = g ∘ h ∘ f` for `h` the cocycle of
`actionDefect`. -/
lemma δ_actionMid (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    δ 0 1 (actionMid hw k k' hk) =
      (Cochain.ofHom (grShortComplexFunctorMap F M k).g).comp
        ((Cocycle.equivHomShift (actionDefect hw' k k' hk)).1.comp
          (Cochain.ofHom ((grShortComplexFunctorMap F M k').f⟦p⟧')) (add_zero 1)) (zero_add 1) := by
  ext n m hnm
  obtain rfl : m = n + 1 := by omega
  rw [δ_v 0 1 rfl _ n (n + 1) hnm n (n + 1) (by omega) rfl, Cochain.zero_cochain_comp_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v,
    ← cancel_epi (F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n))]
  have hπ := fun a b c =>
    map_f_comp_map_d F (cokernel.π (M.succStep (a + 1) ≫ M.succStep a)) b c
  have hd := actionStep_d hw hw' k k' hk n (n + p) (n + 1) (n + 1 + p) rfl rfl rfl
  have hL : F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n) ≫
      ((actionMid hw k k' hk).v n n (add_zero n) ≫
          ((grShortComplexFunctorMap F M k').X₂⟦p⟧).d n (n + 1) +
        Int.negOnePow 1 • (grShortComplexFunctorMap F M k).X₂.d n (n + 1) ≫
          (actionMid hw k k' hk).v (n + 1) (n + 1) (add_zero _)) =
      (p.negOnePow • (actionStep hw k k' hk n (n + p) rfl ≫
          F.map ((M.filtration.obj (op k')).d (n + p) (n + 1 + p))) -
        F.map ((M.filtration.obj (op k)).d n (n + 1)) ≫
          actionStep hw k k' hk (n + 1) (n + 1 + p) rfl) ≫
        F.map ((cokernel.π (M.succStep (k' + 1) ≫ M.succStep k')).f (n + 1 + p)) := by
    simp only [comp_add, Int.negOnePow_one, Units.neg_smul, one_smul, Linear.comp_units_smul,
      comp_neg, sub_comp, Linear.units_smul_comp, assoc, CochainComplex.shiftFunctor_obj_d',
      π_actionMid_v_assoc]
    show p.negOnePow • (_ ≫ F.map ((cokernel.π (M.succStep (k' + 1) ≫ M.succStep k')).f
        (n + p)) ≫ F.map ((M.grShortComplex k').X₂.d (n + p) (n + 1 + p))) +
      -(F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n) ≫
        F.map ((M.grShortComplex k).X₂.d n (n + 1)) ≫ _) = _
    rw [hπ, reassoc_of% hπ, π_actionMid_v, sub_eq_add_neg]
    rfl
  refine hL.trans ?_
  rw [hd]
  show _ = F.map ((cokernel.π (M.succStep (k + 1) ≫ M.succStep k)).f n) ≫
    F.map ((M.grShortComplex k).g.f n) ≫ _ ≫ F.map ((M.grShortComplex k').f.f (n + 1 + p))
  rw [← F.map_comp_assoc, ← HomologicalComplex.comp_f, π_grShortComplex_g]
  simp only [Cocycle.equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero n),
    actionDefect, Cocycle.rightUnshift_coe, Cocycle.ofHom_coe, Cochain.ofHom_v,
    HomologicalComplex.comp_f,
    HomologicalComplex.units_smul_f_apply, Linear.units_smul_comp, Linear.comp_units_smul, assoc,
    CochainComplex.shiftFunctorAdd'_hom_app_f', CochainComplex.shiftFunctorObjXIso,
    mapHomologicalComplex_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    grπ_actionGr_XIsoOfEq_assoc]
  congr 2
  refine ((F.map_comp _ _).symm.trans ?_).trans (congrArg (F.map _ ≫ ·) (id_comp _).symm)
  refine Eq.trans ?_ (F.map_comp _ _)
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, grπ_grShortComplex_f]

/-! ### The Leibniz rule for the connecting morphisms -/

variable [HasDerivedCategory D]

/-- **The Leibniz rule for the connecting morphisms of the graded short exact sequences, in the
derived category.** With `δ_k` the connecting morphism of
`0 ⟶ Φ(gr^{k+1}) ⟶ Φ(F^k/F^{k+2}) ⟶ Φ(gr^k) ⟶ 0` and `δ_{k'}[p]` the one of its translate by `p`,

`μ_w^k ≫ δ_{k'}[p] = δ_k ≫ μ_w^{k+1}[1] + (-1)^p μ_{δw}^k`.

This is `DerivedCategory.map_triangleOfSESδ_of_defect` for the middle cochain `actionMid`. -/
theorem Q_map_actionGr_comp_triangleOfSESδ (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    DerivedCategory.Q.map (actionGr hw hw' k k' hk) ≫
        DerivedCategory.triangleOfSESδ ((grShortComplexFunctorMap_shortExact F M k').map_of_exact
          (CategoryTheory.shiftFunctor (CochainComplex D ℤ) p)) =
      (DerivedCategory.triangleOfSESδ (grShortComplexFunctorMap_shortExact F M k) ≫
          (DerivedCategory.Q.map (actionGr hw hw' (k + 1) (k' + 1) (by omega)))⟦(1 : ℤ)⟧' :
            DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((FilteredObject.gr k).obj M)) ⟶
              (DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((FilteredObject.gr (k' + 1)).obj M))⟦p⟧))⟦(1 : ℤ)⟧) +
        (DerivedCategory.Q.map (actionDefect hw' k k' hk) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _ :
            DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((FilteredObject.gr k).obj M)) ⟶
              (DerivedCategory.Q.obj (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((FilteredObject.gr (k' + 1)).obj M))⟦p⟧))⟦(1 : ℤ)⟧) := by
  have h := DerivedCategory.map_triangleOfSESδ_of_defect
    (S := grShortComplexFunctorMap F M k)
    (T := (grShortComplexFunctorMap F M k').map
      (CategoryTheory.shiftFunctor (CochainComplex D ℤ) p))
    (actionGr hw hw' (k + 1) (k' + 1) (by omega)) (actionMid hw k k' hk)
    (actionGr hw hw' k k' hk) (Cocycle.equivHomShift (actionDefect hw' k k' hk))
    (grShortComplexFunctorMap_shortExact F M k)
    ((grShortComplexFunctorMap_shortExact F M k').map_of_exact
      (CategoryTheory.shiftFunctor (CochainComplex D ℤ) p))
    (ofHom_f_comp_actionMid hw hw' k k' hk) (actionMid_comp_ofHom_g hw hw' k k' hk)
    (δ_actionMid hw hw' k k' hk)
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-! ### Composition and linearity of the maps induced on a shift sequence -/

section ShiftMap

variable {T : Type*} [Category* T] [HasShift T ℤ] {Ab : Type*} [Category* Ab]
  [Preadditive T] [Preadditive Ab] (H : T ⥤ Ab) [H.ShiftSequence ℤ]

omit [Preadditive T] [Preadditive Ab] in
/-- **Two maps induced on a shift sequence compose to the map induced by the composite**: for
`β : X ⟶ Y[a]` and `γ : Y ⟶ Z[b]`, `β ≫ γ[a]` read in `Z[c]`, `b + a = c`. -/
lemma _root_.CategoryTheory.Functor.shiftMap_comp_shiftMap {X Y Z : T} {a b : ℤ} (β : X ⟶ Y⟦a⟧)
    (γ : Y ⟶ Z⟦b⟧) (c : ℤ) (hc : b + a = c) {n n₁ n₂ : ℤ} (h₁ : a + n = n₁)
    (h₂ : b + n₁ = n₂) :
    H.shiftMap β n n₁ h₁ ≫ H.shiftMap γ n₁ n₂ h₂ =
      H.shiftMap (β ≫ γ⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' T b a c hc).inv.app Z) n n₂
        (show c + n = n₂ by omega) := by
  simp only [Functor.shiftMap, Functor.map_comp, assoc]
  have hn := (H.shiftIso a n n₁ h₁).hom.naturality γ
  dsimp at hn
  rw [← reassoc_of% hn, H.shiftIso_hom_app_comp a b c hc n n₁ n₂ h₁ h₂]

/-- The map induced on a shift sequence by `e • β`, for a unit `e : ℤˣ`, is `e` times the map
induced by `β`. -/
lemma _root_.CategoryTheory.Functor.shiftMap_units_smul {X Y : T} {a : ℤ} (e : ℤˣ)
    (β : X ⟶ Y⟦a⟧) (n n₁ : ℤ) (h : a + n = n₁) [(H.shift n).Additive] :
    H.shiftMap (e • β) n n₁ h = e • H.shiftMap β n n₁ h := by
  simp only [Functor.shiftMap, Functor.map_units_smul, Linear.units_smul_comp]

end ShiftMap

/-! ### After a functor of derived categories -/

section Derived

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (G : DerivedCategory D ⥤ DerivedCategory B) [G.CommShift ℤ] [G.Additive]

variable (F M) in
/-- `G` of the connecting morphism of `0 ⟶ Φ(gr^{k+1}) ⟶ Φ(F^k/F^{k+2}) ⟶ Φ(gr^k) ⟶ 0`, with the
commutation of `G` with the shift. -/
abbrev derivedConnecting (k : ℤ) :
    (DerivedCategory.Q ⋙ G).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k).obj M)) ⟶
      ((DerivedCategory.Q ⋙ G).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((FilteredObject.gr (k + 1)).obj M)))⟦(1 : ℤ)⟧ :=
  G.map (DerivedCategory.triangleOfSESδ (grShortComplexFunctorMap_shortExact F M k)) ≫
    (G.commShiftIso (1 : ℤ)).hom.app _

/-- `G` of a morphism of complexes `u : K ⟶ L[s]`, read as a morphism `G(K) ⟶ G(L)[s]`. -/
abbrev derivedShiftedMap {K L : CochainComplex D ℤ} {s : ℤ} (u : K ⟶ L⟦s⟧) :
    (DerivedCategory.Q ⋙ G).obj K ⟶ ((DerivedCategory.Q ⋙ G).obj L)⟦s⟧ :=
  (DerivedCategory.Q ⋙ G).map u ≫ ((DerivedCategory.Q ⋙ G).commShiftIso s).hom.app L

/-- **The Leibniz rule of the connecting morphisms, after a functor of derived categories**:
`μ_w^k ∘ δ_{k'} = (-1)^p δ_k ∘ μ_w^{k+1} + μ_{δw}^k`, each composite of a morphism to a
`[p]` and one to a `[1]` read in `[p + 1]` through the canonical isomorphisms. -/
theorem derivedShiftedMap_actionGr_comp_derivedConnecting (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') :
    derivedShiftedMap G (actionGr hw hw' k k' hk) ≫ (derivedConnecting F M G k')⟦p⟧' ≫
        (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) 1 p (p + 1) (by omega)).inv.app
          ((DerivedCategory.Q ⋙ G).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((FilteredObject.gr (k' + 1)).obj M))) =
      derivedShiftedMap G (actionGr hw' respectsFiltration_δ_δ k (k' + 1) (by omega)) +
        (p.negOnePow • (derivedConnecting F M G k ≫
          (derivedShiftedMap G (actionGr hw hw' (k + 1) (k' + 1) (by omega)))⟦(1 : ℤ)⟧' ≫
            (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
          ((DerivedCategory.Q ⋙ G).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((FilteredObject.gr (k' + 1)).obj M)))) : (DerivedCategory.Q ⋙ G).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k).obj M)) ⟶
              (((DerivedCategory.Q ⋙ G).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((FilteredObject.gr (k' + 1)).obj M))))⟦p + 1⟧) := by
  have E0 := Q_map_actionGr_comp_triangleOfSESδ hw hw' k k' hk
  set H := DerivedCategory.Q ⋙ G with hH
  set B₀ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr k').obj M)
  set B₁ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr (k' + 1)).obj M)
  set δT := DerivedCategory.triangleOfSESδ
    ((grShortComplexFunctorMap_shortExact F M k').map_of_exact
    (CategoryTheory.shiftFunctor (CochainComplex D ℤ) p))
  have hS : G.map δT ≫ (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) =
      p.negOnePow • ((H.commShiftIso p).hom.app B₀ ≫ (derivedConnecting F M G k')⟦p⟧' ≫
        (shiftFunctorComm (DerivedCategory B) 1 p).hom.app (H.obj B₁) ≫
          ((H.commShiftIso p).inv.app B₁)⟦(1 : ℤ)⟧') :=
    DerivedCategory.map_triangleOfSESδ_shift G (grShortComplexFunctorMap_shortExact F M k') p
  have hcomm : (shiftFunctorComm (DerivedCategory B) 1 p).hom.app (H.obj B₁) ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app (H.obj B₁) =
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) 1 p (p + 1) (by omega)).inv.app
        (H.obj B₁) := by
    rw [shiftFunctorComm_eq _ 1 p (p + 1) (by omega)]
    simp
  have step₁ : (H.commShiftIso p).hom.app B₀ ≫ (derivedConnecting F M G k')⟦p⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) 1 p (p + 1) (by omega)).inv.app
        (H.obj B₁) =
      p.negOnePow • (G.map δT ≫ (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) ≫
        ((H.commShiftIso p).hom.app B₁)⟦(1 : ℤ)⟧' ≫
          (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
            (H.obj B₁)) := by
    rw [← assoc (G.map δT), hS]
    simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul, assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    refine congrArg (fun x => _ ≫ _ ≫ x) ?_
    show _ = (shiftFunctorComm (DerivedCategory B) 1 p).hom.app (H.obj B₁) ≫
      (CategoryTheory.shiftFunctor (DerivedCategory B) 1).map (𝟙 ((H.obj B₁)⟦p⟧)) ≫ _
    rw [CategoryTheory.Functor.map_id]
    exact hcomm.symm.trans (congrArg (fun x => _ ≫ x) (id_comp _).symm)
  have hadd : H.map ((CategoryTheory.shiftFunctorAdd' (CochainComplex D ℤ) p 1 (p + 1) rfl).hom.app
        B₁) ≫ (H.commShiftIso (1 : ℤ)).hom.app (B₁⟦p⟧) ≫ ((H.commShiftIso p).hom.app B₁)⟦1⟧' ≫
        (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app (H.obj B₁) =
      (H.commShiftIso (p + 1)).hom.app B₁ := by
    rw [Functor.commShiftIso_add' H (show p + 1 = p + 1 from rfl),
      Functor.CommShift.isoAdd'_hom_app]
  have E1 := congrArg (fun x => G.map x ≫ (G.commShiftIso (1 : ℤ)).hom.app _ ≫
    ((H.commShiftIso p).hom.app B₁)⟦1⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app (H.obj B₁)) E0
  simp only [Functor.map_comp, Functor.map_add, add_comp, assoc] at E1
  have hL : derivedShiftedMap G (actionGr hw hw' k k' hk) ≫ (derivedConnecting F M G k')⟦p⟧' ≫
      (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) 1 p (p + 1) (by omega)).inv.app
        (H.obj B₁) =
      p.negOnePow • (G.map (DerivedCategory.Q.map (actionGr hw hw' k k' hk)) ≫ G.map δT ≫
        (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) ≫
          ((H.commShiftIso p).hom.app B₁)⟦(1 : ℤ)⟧' ≫
            (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
              (H.obj B₁)) := by
    simp only [derivedShiftedMap, assoc]
    rw [step₁, Linear.comp_units_smul]
    rfl
  rw [hL, E1]
  have hR1 : G.map (DerivedCategory.triangleOfSESδ (grShortComplexFunctorMap_shortExact F M k)) ≫
      G.map ((DerivedCategory.Q.map (actionGr hw hw' (k + 1) (k' + 1) (by omega)))⟦(1 : ℤ)⟧') ≫
        (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) ≫
          ((H.commShiftIso p).hom.app B₁)⟦(1 : ℤ)⟧' ≫
            (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
              (H.obj B₁) =
      derivedConnecting F M G k ≫
        (derivedShiftedMap G (actionGr hw hw' (k + 1) (k' + 1) (by omega)))⟦(1 : ℤ)⟧' ≫
          (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
            (H.obj B₁) := by
    have hn : G.map ((DerivedCategory.Q.map (actionGr hw hw' (k + 1) (k' + 1) (by omega)))⟦1⟧') ≫
        (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) =
        (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((FilteredObject.gr (k + 1)).obj M))) ≫
          (G.map (DerivedCategory.Q.map (actionGr hw hw' (k + 1) (k' + 1) (by omega))))⟦1⟧' :=
      (G.commShiftIso (1 : ℤ)).hom.naturality _
    rw [reassoc_of% hn]
    simp only [derivedConnecting, derivedShiftedMap, Functor.map_comp, assoc]
    rfl
  have hR2 : G.map (DerivedCategory.Q.map (actionDefect hw' k k' hk)) ≫
      G.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (B₁⟦p⟧)) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj (B₁⟦p⟧)) ≫
          ((H.commShiftIso p).hom.app B₁)⟦(1 : ℤ)⟧' ≫
            (CategoryTheory.shiftFunctorAdd' (DerivedCategory B) p 1 (p + 1) rfl).inv.app
              (H.obj B₁) =
      p.negOnePow • derivedShiftedMap G (actionGr hw' respectsFiltration_δ_δ k (k' + 1)
        (by omega)) := by
    simp only [actionDefect, Functor.map_units_smul, Linear.units_smul_comp, Functor.map_comp,
      assoc, derivedShiftedMap]
    congr 1
    rw [← hadd, show (H.commShiftIso (1 : ℤ)).hom.app (B₁⟦p⟧) =
      G.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (B₁⟦p⟧)) ≫
        (G.commShiftIso (1 : ℤ)).hom.app _ from Functor.commShiftIso_comp_hom_app _ _ _ _]
    simp only [assoc]
    rfl
  rw [hR1, hR2, smul_add, smul_smul, Int.units_mul_self, one_smul]
  exact add_comm _ _

/-- **The Leibniz rule of the connecting morphisms, on cohomology**: for `n + p = n₁`, the map
`Hⁿ(G Φ gr^k) ⟶ H^{n₁}(G Φ gr^{k'}) ⟶ H^{n₁+1}(G Φ gr^{k'+1})` induced by `μ_w^k` and the
connecting morphism is `μ_{δw}^k + (-1)^p (μ_w^{k+1} ∘ δ_k)`. -/
theorem shiftMap_actionGr_comp_derivedConnecting (hw : RespectsFiltration F M w)
    (hw' : RespectsFiltration F M (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k')
    (n n₁ n₂ n₃ : ℤ) (h₁ : p + n = n₁) (h₂ : 1 + n₁ = n₂) (h₃ : 1 + n = n₃) (h₄ : p + n₃ = n₂) :
    (DerivedCategory.homologyFunctor B 0).shiftMap
        (derivedShiftedMap G (actionGr hw hw' k k' hk)) n n₁ h₁ ≫
      (DerivedCategory.homologyFunctor B 0).shiftMap (derivedConnecting F M G k') n₁ n₂ h₂ =
    (DerivedCategory.homologyFunctor B 0).shiftMap
        (derivedShiftedMap G (actionGr hw' respectsFiltration_δ_δ k (k' + 1) (by omega)))
          n n₂ (by omega) +
      p.negOnePow • ((DerivedCategory.homologyFunctor B 0).shiftMap
          (derivedConnecting F M G k) n n₃ h₃ ≫
        (DerivedCategory.homologyFunctor B 0).shiftMap
          (derivedShiftedMap G (actionGr hw hw' (k + 1) (k' + 1) (by omega))) n₃ n₂ h₄) := by
  rw [Functor.shiftMap_comp_shiftMap _ _ _ (p + 1) (by omega),
    Functor.shiftMap_comp_shiftMap _ _ _ (p + 1) rfl,
    derivedShiftedMap_actionGr_comp_derivedConnecting, ← Functor.shiftMap_units_smul]
  simp only [Functor.shiftMap, Functor.map_add, add_comp]

variable [HasDerivedCategory C]

variable (F M) in
/-- **The connecting morphism of the graded sequence of `Φ(K)` is `Φ` of the one of `K`**: the
image under `Φ` on derived categories of the connecting morphism of
`0 ⟶ gr^{k+1} ⟶ F^k/F^{k+2} ⟶ gr^k ⟶ 0`, read through the identification of `Φ` on derived
categories with `Φ` on complexes, is the connecting morphism of the image sequence. -/
lemma mapDerivedCategory_map_triangleOfSESδ (k : ℤ) :
    F.mapDerivedCategory.map (DerivedCategory.triangleOfSESδ (M.grShortComplex_shortExact k)) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ =
      F.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.triangleOfSESδ (grShortComplexFunctorMap_shortExact F M k) ≫
          (F.mapDerivedCategoryFactors.inv.app ((FilteredObject.gr (k + 1)).obj M))⟦(1 : ℤ)⟧' := by
  rw [DerivedCategory.map_triangleOfSESδ]
  simp only [assoc, Iso.inv_hom_id_app]
  exact congrArg (fun x => _ ≫ _ ≫ x) (comp_id _)

end Derived

end CochainComplex.Filtered
