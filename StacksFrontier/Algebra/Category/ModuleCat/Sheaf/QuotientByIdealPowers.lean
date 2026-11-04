module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedConstancy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdeal

/-!
# Multiplication maps between quotients of a sheaf of modules by powers of an ideal

Let `(C, J)` be a site, `Λ` a commutative ring and `F` a sheaf of `Λ`-modules. A quotient map
`q : F ⟶ G` by an ideal `I` (`Stacks.ModuleSheaf.IsQuotientBy`) is an epimorphism, and maps out
of `G` are produced from maps out of `F` with a suitable annihilation property, without ever
constructing `IF` or `F / IF`:

* for an element `a` with `I a ⊆ I'` and a map `q' : F ⟶ G'` to a sheaf annihilated by `I'`,
  the map `a • q'` factors uniquely through `q`; for `F / IⁿF ⟶ F / Iⁿ⁺¹F` and `a ∈ I` this is
  multiplication by `a`, the map `IⁿF / Iⁿ⁺¹F ⟶ Iⁿ⁺¹F / Iⁿ⁺²F` of the source on graded pieces;
* a map `h` out of a quotient `G'` of `F` factors through a further quotient `G` of `G'` by `I`
  as soon as `I` kills the composite `F ⟶ G' ⟶ T`.

The second statement says in particular that the kernel of `F / Iⁿ⁺¹F ⟶ F / IⁿF` is generated
by the images of the maps `F ⟶ F / Iⁿ⁺¹F` given by multiplication by the elements of `Iⁿ`.

## Main results

* `Stacks.ModuleSheaf.IsQuotientBy.epi`: a quotient map is an epimorphism.
* `Stacks.ModuleSheaf.IsQuotientBy.existsUnique_comp_eq_smul`: the factorization of `a • q'`.
* `Stacks.ModuleSheaf.IsQuotientBy.exists_eq_comp_of_smul_eq_zero`: the factorization through a
  further quotient.

## References

* [Stacks Project, Tag 09BU](https://stacks.math.columbia.edu/tag/09BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ConstantSheaf (pathHom)

universe w v u r

namespace Stacks.ModuleSheaf

/-- If `q' ≫ t` is the quotient map by `I`, then `t` kills `b • q'` for every `b ∈ I`. -/
private theorem smul_comp_eq_zero_of_isQuotientBy {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {Λ : Type r} [CommRing Λ] {I : Ideal Λ}
    {F G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G} (h : IsQuotientBy J Λ I F G q)
    {G' : Sheaf J (ModuleCat.{w} Λ)} (q' : F ⟶ G') (t : G' ⟶ G) (ht : q' ≫ t = q) {b : Λ}
    (hb : b ∈ I) : (b • q') ≫ t = 0 := by
  rw [Linear.smul_comp, ht, ← Category.comp_id q, ← Linear.comp_smul,
    (isAnnihilatedBy_iff_smul_id _ G).mp h.1 b hb, comp_zero]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Λ : Type r} [CommRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]

/-- The image of a morphism of sheaves of modules is annihilated by an ideal which kills the
morphism. -/
theorem isAnnihilatedBy_image {I : Ideal Λ} {G G' : Sheaf J (ModuleCat.{w} Λ)} (g : G ⟶ G')
    (hg : ∀ b ∈ I, b • g = 0) : IsAnnihilatedBy J Λ I (Abelian.image g) := by
  have := Abelian.instEpiFactorThruImage g
  have : Mono (Abelian.image.ι g) := equalizer.ι_mono
  rw [isAnnihilatedBy_iff_smul_id]
  intro b hb
  rw [← cancel_epi (Abelian.factorThruImage g), ← cancel_mono (Abelian.image.ι g)]
  simp only [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Abelian.image.fac, comp_zero,
    zero_comp]
  exact hg b hb

variable {I : Ideal Λ} {F G : Sheaf J (ModuleCat.{w} Λ)} {q : F ⟶ G}

/-- **A quotient map by an ideal is an epimorphism**: a map out of the quotient killed by the
quotient map has an image annihilated by the ideal, through which the quotient map factors in two
ways. -/
theorem IsQuotientBy.epi (h : IsQuotientBy J Λ I F G q) : Epi q := by
  refine Preadditive.epi_of_cancel_zero _ fun {T} g hg ↦ ?_
  have hG := (isAnnihilatedBy_iff_smul_id I G).mp h.1
  have hIm := isAnnihilatedBy_image g fun b hb ↦ by
    rw [← Category.id_comp g, ← Linear.smul_comp, hG b hb, zero_comp]
  have : Mono (Abelian.image.ι g) := equalizer.ι_mono
  have h0 : q ≫ Abelian.factorThruImage g = 0 := by
    rw [← cancel_mono (Abelian.image.ι g), Category.assoc, Abelian.image.fac, hg, zero_comp]
  obtain ⟨d, -, hd⟩ := h.2 _ hIm (q ≫ Abelian.factorThruImage g)
  have e1 := hd (Abelian.factorThruImage g) rfl
  have e2 := hd 0 (comp_zero.trans h0.symm)
  rw [← Abelian.image.fac g, e1.trans e2.symm, zero_comp]

/-- **Multiplication by an element on quotients.** Let `q : F ⟶ G` be the quotient by `I` and
`q' : F ⟶ G'` a map to a sheaf annihilated by `I'`. If `b * a ∈ I'` for every `b ∈ I`, then
`a • q'` factors uniquely through `q`. -/
theorem IsQuotientBy.existsUnique_comp_eq_smul (h : IsQuotientBy J Λ I F G q) {I' : Ideal Λ}
    {G' : Sheaf J (ModuleCat.{w} Λ)} (hG' : IsAnnihilatedBy J Λ I' G') (q' : F ⟶ G') (a : Λ)
    (ha : ∀ b ∈ I, b * a ∈ I') : ∃! ψ : G ⟶ G', q ≫ ψ = a • q' := by
  have hG'' := (isAnnihilatedBy_iff_smul_id I' G').mp hG'
  have hIm := isAnnihilatedBy_image (a • 𝟙 G') fun b hb ↦ by
    rw [smul_smul, hG'' _ (ha b hb)]
  obtain ⟨d, hd, -⟩ := h.2 _ hIm (q' ≫ Abelian.factorThruImage (a • 𝟙 G'))
  have := h.epi
  have key : q ≫ d ≫ Abelian.image.ι _ = a • q' := by
    rw [← Category.assoc, hd, Category.assoc, Abelian.image.fac, Linear.comp_smul, Category.comp_id]
  refine ⟨d ≫ Abelian.image.ι _, ?_, fun ψ hψ ↦ ?_⟩
  · exact key
  · rw [← cancel_epi q, hψ, key]

/-- **Factorization through a further quotient.** Let `q' : F ⟶ G'` be an epimorphism and
`t : G' ⟶ G` a map with `q' ≫ t = q` the quotient by `I`. A map `h : G' ⟶ T` factors through `t`
as soon as `b • (q' ≫ h) = 0` for every `b ∈ I`. -/
theorem IsQuotientBy.exists_eq_comp_of_smul_eq_zero (h : IsQuotientBy J Λ I F G q)
    {G' : Sheaf J (ModuleCat.{w} Λ)} (q' : F ⟶ G') [Epi q'] (t : G' ⟶ G) (ht : q' ≫ t = q)
    {T : Sheaf J (ModuleCat.{w} Λ)} (k : G' ⟶ T) (hk : ∀ b ∈ I, b • (q' ≫ k) = 0) :
    ∃ d : G ⟶ T, k = t ≫ d := by
  have hIm := isAnnihilatedBy_image (q' ≫ k) hk
  obtain ⟨d, hd, -⟩ := h.2 _ hIm (Abelian.factorThruImage (q' ≫ k))
  refine ⟨d ≫ Abelian.image.ι _, ?_⟩
  rw [← cancel_epi q', ← Category.assoc q' t, ht, ← Category.assoc, hd, Abelian.image.fac]

/-- **The kernel of a transition map between quotients is generated by multiples.** Let
`q' : F ⟶ G'` be an epimorphism and `t : G' ⟶ G` a map with `q' ≫ t = q` the quotient by the ideal
spanned by a set `s`. For `b ∈ s` the map `b • q'` lands in the kernel of `t`; a map out of that
kernel killing all of these vanishes. For `G' = F / Iⁿ⁺¹F` and `s` a set of generators of `Iⁿ`
this says that `IⁿF / Iⁿ⁺¹F` is generated by the multiples of the sections of `F` by the elements
of `s`. -/
theorem IsQuotientBy.eq_zero_of_kernelLift_comp_eq_zero {s : Set Λ}
    (h : IsQuotientBy J Λ (Ideal.span s) F G q) {G' : Sheaf J (ModuleCat.{w} Λ)} (q' : F ⟶ G')
    [Epi q'] (t : G' ⟶ G) (ht : q' ≫ t = q) {T : Sheaf J (ModuleCat.{w} Λ)} (k : kernel t ⟶ T)
    (hk : ∀ (b : Λ) (hb : b ∈ s),
      kernel.lift t (b • q') (by
        rw [Linear.smul_comp, ht, ← Category.comp_id q, ← Linear.comp_smul,
          (isAnnihilatedBy_iff_smul_id _ G).mp h.1 b (Ideal.subset_span hb), comp_zero]) ≫ k = 0) :
    k = 0 := by
  have := Abelian.mono_pushout_of_mono_f (kernel.ι t) k
  have hs : ∀ b ∈ Ideal.span s, b • (q' ≫ pushout.inl (kernel.ι t) k) = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      rw [← Linear.smul_comp, ← kernel.lift_ι t (x • q')
        (smul_comp_eq_zero_of_isQuotientBy h q' t ht (Ideal.subset_span hx)), Category.assoc,
        pushout.condition, ← Category.assoc, hk x hx, zero_comp]
    | zero => exact zero_smul _ _
    | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]
  obtain ⟨d, hd⟩ := h.exists_eq_comp_of_smul_eq_zero q' t ht (pushout.inl (kernel.ι t) k) hs
  rw [← cancel_mono (pushout.inr (kernel.ι t) k), ← pushout.condition, hd, ← Category.assoc,
    kernel.condition, zero_comp, zero_comp]

/-! ### The graded pieces of the tower of quotients by the powers of an ideal -/

section Graded

/-- The transition map `F / Iⁿ⁺¹F ⟶ F / IⁿF` of a tower of quotients. -/
abbrev towerMap (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ)) (n : ℕ) :
    Q.obj (op (n + 1)) ⟶ Q.obj (op n) :=
  Q.map (homOfLE (Nat.le_succ n)).op

/-- The graded piece `IⁿF / Iⁿ⁺¹F`, the kernel of the transition map. -/
abbrev gradedPiece (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ)) (n : ℕ) : Sheaf J (ModuleCat.{w} Λ) :=
  kernel (towerMap Q n)

variable (I : Ideal Λ) {Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ)}
  (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
  (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))

include hq in
omit [HasSheafify J (ModuleCat Λ)] in
theorem app_comp_towerMap (n : ℕ) : q.app (op (n + 1)) ≫ towerMap Q n = q.app (op n) := by
  have := q.naturality (homOfLE (Nat.le_succ n)).op
  simpa using this.symm

include hq in
theorem exists_comp_eq_smul_tower (a : Λ) (ha : a ∈ I) (n : ℕ) :
    ∃! m : Q.obj (op n) ⟶ Q.obj (op (n + 1)), q.app (op n) ≫ m = a • q.app (op (n + 1)) :=
  (hq n).existsUnique_comp_eq_smul (hq (n + 1)).1 _ a fun b hb => by
    rw [pow_succ]; exact Ideal.mul_mem_mul hb ha

/-- Multiplication by `a ∈ I` as a map `F / IⁿF ⟶ F / Iⁿ⁺¹F`. -/
noncomputable def towerMul (a : Λ) (ha : a ∈ I) (n : ℕ) : Q.obj (op n) ⟶ Q.obj (op (n + 1)) :=
  (exists_comp_eq_smul_tower I q hq a ha n).exists.choose

theorem app_comp_towerMul (a : Λ) (ha : a ∈ I) (n : ℕ) :
    q.app (op n) ≫ towerMul I q hq a ha n = a • q.app (op (n + 1)) :=
  (exists_comp_eq_smul_tower I q hq a ha n).exists.choose_spec

theorem towerMap_comp_towerMul (a : Λ) (ha : a ∈ I) (n : ℕ) :
    towerMap Q n ≫ towerMul I q hq a ha n = towerMul I q hq a ha (n + 1) ≫ towerMap Q (n + 1) := by
  have := (hq (n + 1)).epi
  rw [← cancel_epi (q.app (op (n + 1))), ← Category.assoc, app_comp_towerMap I q hq,
    app_comp_towerMul, ← Category.assoc, app_comp_towerMul, Linear.smul_comp,
    app_comp_towerMap I q hq]

theorem towerMul_comm (a b : Λ) (ha : a ∈ I) (hb : b ∈ I) (n : ℕ) :
    towerMul I q hq a ha n ≫ towerMul I q hq b hb (n + 1) =
      towerMul I q hq b hb n ≫ towerMul I q hq a ha (n + 1) := by
  have := (hq n).epi
  rw [← cancel_epi (q.app (op n)), ← Category.assoc, ← Category.assoc, app_comp_towerMul,
    app_comp_towerMul, Linear.smul_comp, Linear.smul_comp, app_comp_towerMul, app_comp_towerMul,
    smul_smul, smul_smul, mul_comm]

/-- Multiplication by `a ∈ I` on graded pieces, `IⁿF / Iⁿ⁺¹F ⟶ Iⁿ⁺¹F / Iⁿ⁺²F`. -/
noncomputable def gradedMul (a : Λ) (ha : a ∈ I) (n : ℕ) :
    gradedPiece Q n ⟶ gradedPiece Q (n + 1) :=
  kernel.lift _ (kernel.ι _ ≫ towerMul I q hq a ha (n + 1)) (by
    rw [Category.assoc, ← towerMap_comp_towerMul, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem gradedMul_ι (a : Λ) (ha : a ∈ I) (n : ℕ) :
    gradedMul I q hq a ha n ≫ kernel.ι _ = kernel.ι _ ≫ towerMul I q hq a ha (n + 1) :=
  kernel.lift_ι _ _ _

theorem gradedMul_comm (a b : Λ) (ha : a ∈ I) (hb : b ∈ I) (n : ℕ) :
    gradedMul I q hq a ha n ≫ gradedMul I q hq b hb (n + 1) =
      gradedMul I q hq b hb n ≫ gradedMul I q hq a ha (n + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, gradedMul_ι, gradedMul_ι_assoc, towerMul_comm]

/-- The ideal generated by the products of `n` members of a family is the `n`-th power of the
ideal generated by the family. -/
theorem span_range_prod_eq_pow {k : ℕ} (μ : Fin k → Λ) (n : ℕ) :
    Ideal.span (Set.range fun w : Fin n → Fin k => ∏ i, μ (w i)) =
      Ideal.span (Set.range μ) ^ n := by
  induction n with
  | zero =>
    have : (Set.range fun w : Fin 0 → Fin k => ∏ i, μ (w i)) = {1} := by
      ext x; simp
    rw [this, Ideal.span_singleton_one, pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [pow_succ, ← ih, Ideal.span_mul_span']
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_mul]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨Fin.init w, rfl⟩, _, ⟨w (Fin.last n), rfl⟩,
        (Fin.prod_univ_castSucc (fun i => μ (w i))).symm⟩
    · rintro ⟨_, ⟨w', rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨Fin.snoc w' j, by simp [Fin.prod_univ_castSucc]⟩

include hq in
omit [HasSheafify J (ModuleCat Λ)] in
theorem app_zero_eq_zero : q.app (op 0) = 0 := by
  have h := (isAnnihilatedBy_iff_smul_id _ (Q.obj (op 0))).mp (hq 0).1 1 (by simp)
  rw [one_smul] at h
  rw [← Category.comp_id (q.app (op 0)), h, comp_zero]

variable {k : ℕ} (μ : Fin k → Λ) (hμ : ∀ j, μ j ∈ I)

/-- The map `F ⟶ F / IF`, into the graded piece of degree `0`. -/
noncomputable def toGradedPieceZero : F ⟶ gradedPiece Q 0 :=
  kernel.lift _ (q.app (op 1)) (by rw [app_comp_towerMap I q hq, app_zero_eq_zero I q hq])

theorem toGradedPieceZero_pathHom_ι {n : ℕ} (w : Fin n → Fin k) :
    (toGradedPieceZero I q hq ≫
        pathHom (fun j n => gradedMul I q hq (μ j) (hμ j) n) w) ≫ kernel.ι _ =
      (∏ i, μ (w i)) • q.app (op (n + 1)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    exact kernel.lift_ι _ _ _
  | succ n ih =>
    show (toGradedPieceZero I q hq ≫ (pathHom _ (Fin.init w) ≫ gradedMul I q hq _ _ n)) ≫
      kernel.ι _ = _
    rw [Category.assoc, Category.assoc, gradedMul_ι, ← Category.assoc, ← Category.assoc]
    rw [ih (Fin.init w), Linear.smul_comp,
      app_comp_towerMul, smul_smul, Fin.prod_univ_castSucc]
    rfl

/-- **The graded pieces are generated by the multiples of `F / IF`.** If `μ` generates `I`, a map
out of `IⁿF / Iⁿ⁺¹F` vanishing on the images of all composites of `n` multiplications by members
of `μ` vanishes. -/
theorem gradedPiece_hom_ext (hI : Ideal.span (Set.range μ) = I) {n : ℕ}
    {Z : Sheaf J (ModuleCat.{w} Λ)} (g : gradedPiece Q n ⟶ Z)
    (hg : ∀ w : Fin n → Fin k,
      pathHom (fun j n => gradedMul I q hq (μ j) (hμ j) n) w ≫ g = 0) : g = 0 := by
  have hspan : Ideal.span (Set.range fun w : Fin n → Fin k => ∏ i, μ (w i)) = I ^ n := by
    rw [span_range_prod_eq_pow, hI]
  have h := hq n
  rw [← hspan] at h
  have := (hq (n + 1)).epi
  refine h.eq_zero_of_kernelLift_comp_eq_zero (q.app (op (n + 1))) (towerMap Q n)
    (app_comp_towerMap I q hq n) g fun b hb => ?_
  obtain ⟨w, rfl⟩ := hb
  have hl : kernel.lift (towerMap Q n) ((∏ i, μ (w i)) • q.app (op (n + 1)))
      (smul_comp_eq_zero_of_isQuotientBy h _ _ (app_comp_towerMap I q hq n)
        (Ideal.subset_span ⟨w, rfl⟩)) =
      toGradedPieceZero I q hq ≫ pathHom (fun j n => gradedMul I q hq (μ j) (hμ j) n) w := by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, toGradedPieceZero_pathHom_ι]
  rw [hl, Category.assoc, hg w, comp_zero]

end Graded

end Stacks.ModuleSheaf

end
