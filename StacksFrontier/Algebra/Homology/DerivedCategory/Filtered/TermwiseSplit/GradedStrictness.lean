module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.AcyclicHomotopy

/-!
# Lifting short exact sequences of finite filtered objects to termwise split sequences

Let `𝒜` be an abelian category and `0 → A → B → C → 0` a short exact sequence of `Fil^f(𝒜)`, and
let `a : A[0] ⟶ I^•`, `c : C[0] ⟶ J^•` be filtered quasi-isomorphisms into complexes of finitely
filtered objects vanishing in negative degrees, with each `I^n` filtered injective. Then the
sequence lifts: there are `M^•`, `u : I^• ⟶ M^•`, `v : M^• ⟶ J^•` and `b : B[0] ⟶ M^•` with
`0 → I^• → M^• → J^• → 0` short exact and termwise split in `Fil(𝒜)`, and both squares commuting.

`M^•` is a *twisted sum* of `I^•` and `J^•` (`Twist`, `twistedSumFiltered`): the underlying graded
object is the direct sum, the differential is `(d_I, δ, d_J)` for a degreewise family
`δ^n : J^n ⟶ I^{n + 1}` of filtered components satisfying the anticommutation that makes the total
differential square to zero, and the filtration is the direct sum of the two filtrations, twisted
by the same family. Termwise splitness is then automatic, `u` and `v` being the inclusion and the
projection, and short exactness is the corresponding statement for a biproduct. What has to be
produced is the family `δ` together with the comparison `b`, and that is the source's argument: the
composite `B[0] ⟶ C[0] ⟶ J^•` is filtered, `I^•` is filtered injective, so a filtered lift of each
obstruction exists degree by degree (`exists_twistStep`), and the recursion assembles them
(`twistFamily`, `exists_twist`).

The strictness the construction consumes at three places is `isStrictHom_evalFunctor_map_of_*`: a
morphism of finitely filtered objects whose graded pieces form a short exact sequence, or which is
a filtered quasi-isomorphism in each degree, is strict. Both are proved from the exactness of the
associated graded by descending induction on the filtration, which is where the finiteness
hypothesis enters.

This file holds the first part of the construction: the evaluation functor `evalFunctor` and the
differential `evalD` of a filtered complex in a fixed degree, the strictness criterion
[Stacks, Tag 05QH] (4) (`isStrictHom_of_mono_grMap`), and the comparison of graded pieces with
taking terms in a fixed degree. The strictness inputs of the extension steps are in
`TermwiseSplit.ExtensionSteps`, the twisted sum and the main theorem in `TermwiseSplit.TwistedSum`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredTermwiseSplit

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

namespace CochainComplex.FilteredInjective.TermwiseSplit

open CochainComplex.FilteredInjective.Degreewise
open CochainComplex.FilteredInjective.Resolution (filtrationOfSteps homFromDegreeZero
  homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne)

attribute [local simp] evalFil_ι_app homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne

/-- Taking the filtered object in degree `n` is a functor
`Fil(CochainComplex 𝒜 ℤ) ⥤ Fil(𝒜)`. -/
@[implicit_reducible]
noncomputable def evalFunctor (n : ℤ) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ ⥤ FilteredObject 𝒜 ℤᵒᵖ where
  obj K := evalFil K n
  map := fun {K L} f => FilteredObject.homMk (f.hom.f n) (fun i => (f.natTrans.app i).f n)
    (fun i => congrArg (fun g : K.filtration.obj i ⟶ L.X => g.f n) (f.comm i))
  map_id K := by apply FilteredObject.hom_ext; rfl
  map_comp f g := by apply FilteredObject.hom_ext; rfl

@[local simp]
private lemma evalFunctor_map_hom {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f : K ⟶ L)
    (n : ℤ) : ((evalFunctor n).map f).hom = f.hom.f n :=
  rfl

/-- The differential of a filtered complex, as a morphism of filtered objects: the subcomplexes
`F^p K^•` are stable under it. -/
@[implicit_reducible]
public noncomputable def evalD (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    evalFil K n ⟶ evalFil K (n + 1) :=
  FilteredObject.homMk (K.X.d n (n + 1)) (fun i => (K.filtration.obj i).d n (n + 1))
    (fun i => ((K.filtration.ι.app i).comm n (n + 1)).symm)

/-- The underlying morphism of `evalD K n` is the differential `d^n : K^n ⟶ K^{n + 1}`. -/
@[local simp]
public lemma evalD_hom (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    (evalD K n).hom = K.X.d n (n + 1) :=
  rfl

/-! ### Strictness from the graded pieces

The source's construction consumes at three places the strictness of a morphism of filtered
objects, and each time the hypothesis available is one about the graded pieces. The content is
[Stacks, Tag 05QH] (4): *a morphism of `Fil^f(𝒜)` all of whose graded pieces are monomorphisms is
strict.* It is proved here in Mathlib's vocabulary, the only `05QH` in the repository being written
over a different encoding of filtered objects.

The proof is the source's. Strictness at `p` says that `F^p K ⟶ K` is the pullback of
`F^p L ⟶ L` along `f`, which for a square of monomorphisms is equivalent to the induced map on
quotients `K/F^p K ⟶ L/F^p L` being a monomorphism
(`isPullback_of_mono_cokernel_map`, the converse of Mathlib's
`Abelian.mono_cokernel_map_of_isPullback`, which Mathlib does not have). That monomorphy is proved
by induction *upwards* in `p` along the short exact sequences
`0 → gr^p K → K/F^{p + 1} K → K/F^p K → 0` (`exact_quotSeq`, an instance of the
third isomorphism theorem, extracted from Mathlib's exact sequence
`kernelCokernelCompSequence`): the four lemma propagates monomorphy from `gr^p f` and
`K/F^p K ⟶ L/F^p L` to `K/F^{p + 1} K ⟶ L/F^{p + 1} L`, and the induction starts where the
filtration of `K` exhausts `K`, the quotient `K/F^p K` being zero there. Only the exhaustion of
the filtration of `K` is used; nothing is asked of `L`.
-/

/-- A commutative square whose two vertical maps are monomorphisms and whose induced map on their
cokernels is a monomorphism is a pullback square. This is the converse of Mathlib's
`CategoryTheory.Abelian.mono_cokernel_map_of_isPullback`: the pullback of the monomorphism `r`
along `b` is the kernel of `X ⟶ Y ⟶ Y/Q`, which the monomorphy of `X/P ⟶ Y/Q` identifies with the
kernel of `X ⟶ X/P`, namely `P`. -/
public lemma isPullback_of_mono_cokernel_map {P Q X Y : 𝒜} {t : P ⟶ Q} {l : P ⟶ X} {r : Q ⟶ Y}
    {b : X ⟶ Y} [Mono l] [Mono r] (w : l ≫ b = t ≫ r)
    (hn : Mono (cokernel.map l r t b w)) : IsPullback t l r b := by
  have hzero : ∀ s : PullbackCone r b, s.snd ≫ cokernel.π l = 0 := by
    intro s
    refine (cancel_mono (cokernel.map l r t b w)).mp ?_
    rw [zero_comp, Category.assoc, cokernel.π_desc, ← Category.assoc, ← s.condition,
      Category.assoc, cokernel.condition, comp_zero]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w.symm
    (fun s => (ShortComplex.exact_cokernel l).lift s.snd (hzero s)) (fun s => ?_)
    (fun s => (ShortComplex.exact_cokernel l).lift_f s.snd (hzero s)) (fun s m _ hm₂ => ?_))
  · refine (cancel_mono r).mp ?_
    rw [Category.assoc, ← w, ← Category.assoc, ShortComplex.Exact.lift_f, s.condition]
  · refine (cancel_mono l).mp ?_
    rw [hm₂, ShortComplex.Exact.lift_f]

/-- For monomorphisms `u` and `v`, the map `Coker(u) ⟶ Coker(u ≫ v)` is a monomorphism: in
Mathlib's exact sequence `0 → Ker u → Ker (u ≫ v) → Ker v → Coker u → Coker (u ≫ v) → Coker v → 0`
the connecting map is `-Ker(v) ⟶ Coker(u)`, which vanishes because `Ker(v) = 0`. -/
private lemma mono_cokernelMap_id_left {X Y Z : 𝒜} {u : X ⟶ Y} {v : Y ⟶ Z} [Mono v] {w : X ⟶ Z}
    (h : u ≫ v = 𝟙 X ≫ w) : Mono (cokernel.map u w (𝟙 X) v h) := by
  have hw : u ≫ v = w := by rw [h, Category.id_comp]
  subst hw
  have h0 : kernel.ι v = 0 := by rw [← cancel_mono v, zero_comp]; exact kernel.condition v
  have hδ : kernelCokernelCompSequence.δ u v = 0 := by
    rw [kernelCokernelCompSequence.δ_fac, h0, zero_comp, neg_zero]
  exact ((kernelCokernelCompSequence_exact u v).exact 2).mono_g hδ

/-- The third isomorphism theorem: `Coker(u) ⟶ Coker(u ≫ v) ⟶ Coker(v)` is exact. It is the tail
of Mathlib's exact sequence for a composite. -/
private lemma exact_cokernelComp {X Y Z : 𝒜} {u : X ⟶ Y} {v : Y ⟶ Z} {w : X ⟶ Z}
    (h₁ : u ≫ v = 𝟙 X ≫ w) (h₂ : w ≫ 𝟙 Z = u ≫ v) {h₃ : _} :
    (ShortComplex.mk (cokernel.map u w (𝟙 X) v h₁) (cokernel.map w v u (𝟙 Z) h₂) h₃).Exact := by
  have hw : u ≫ v = w := by rw [h₁, Category.id_comp]
  subst hw
  exact (kernelCokernelCompSequence_exact u v).exact 3

/-- The step `F^{p + 1} K ⟶ F^p K` of a filtration. -/
abbrev fstep {C : Type u} [Category.{v} C] (K : FilteredObject C ℤᵒᵖ) (p : ℤ) :
    K.filtration.obj (op (p + 1)) ⟶ K.filtration.obj (op p) :=
  K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op

lemma fstep_comp_ι {C : Type u} [Category.{v} C] (K : FilteredObject C ℤᵒᵖ) (p : ℤ) :
    fstep K p ≫ K.filtration.ι.app (op p) = K.filtration.ι.app (op (p + 1)) :=
  Filtration.diagram_map_comp_ι_app K.filtration _

/-- The graded piece `gr^p K`, spelled as the cokernel of `fstep K p : F^{p + 1} K ⟶ F^p K`.
`(FilteredObject.gr p).obj K` is by definition the cokernel of `K.filtration.step (succHom p)`,
which is `fstep K p` only after unfolding `Filtration.step`; the spelling is repeated so that the
rewriting tactics recognise a term written with it as a cokernel of `fstep K p`. -/
noncomputable abbrev grObj {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredObject C ℤᵒᵖ) (p : ℤ) : C := cokernel (fstep K p)

/-- The map `gr^p f`, in the spelling of `grObj`. -/
noncomputable abbrev grMap {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredObject C ℤᵒᵖ} (f : K ⟶ L) (p : ℤ) :
    grObj K p ⟶ grObj L p :=
  cokernel.map _ _ (f.natTrans.app (op (p + 1))) (f.natTrans.app (op p))
    (f.natTrans.naturality _)

/-- `grMap f p` is `(FilteredObject.gr p).map f`. -/
private lemma mono_grMap_of_mono {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (p : ℤ)
    (h : Mono ((gr p).map f)) : Mono (grMap f p) := h

/-- The map `gr^p K ⟶ K/F^{p + 1} K`. -/
private noncomputable def grToQuot (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    grObj K p ⟶ cokernel (K.filtration.ι.app (op (p + 1))) :=
  cokernel.map _ _ (𝟙 _) (K.filtration.ι.app (op p))
    (by rw [Category.id_comp]; exact fstep_comp_ι K p)

/-- The map `K/F^{p + 1} K ⟶ K/F^p K`. -/
private noncomputable def quotStep (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    cokernel (K.filtration.ι.app (op (p + 1))) ⟶ cokernel (K.filtration.ι.app (op p)) :=
  cokernel.map _ _ (fstep K p) (𝟙 _) (by rw [Category.comp_id]; exact (fstep_comp_ι K p).symm)

/-- The map `K/F^p K ⟶ L/F^p L` induced by a morphism of filtered objects. Strictness at `p` is
exactly the monomorphy of this map. -/
private noncomputable def quotMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (p : ℤ) :
    cokernel (K.filtration.ι.app (op p)) ⟶ cokernel (L.filtration.ι.app (op p)) :=
  cokernel.map _ _ (f.natTrans.app (op p)) f.hom (f.comm (op p)).symm

private lemma π_grToQuot (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    cokernel.π (fstep K p) ≫ grToQuot K p =
      K.filtration.ι.app (op p) ≫ cokernel.π (K.filtration.ι.app (op (p + 1))) :=
  cokernel.π_desc _ _ _

private lemma π_quotStep (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    cokernel.π (K.filtration.ι.app (op (p + 1))) ≫ quotStep K p =
      cokernel.π (K.filtration.ι.app (op p)) := by
  rw [quotStep, cokernel.π_desc, Category.id_comp]

private lemma π_quotMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (p : ℤ) :
    cokernel.π (K.filtration.ι.app (op p)) ≫ quotMap f p =
      f.hom ≫ cokernel.π (L.filtration.ι.app (op p)) :=
  cokernel.π_desc _ _ _

lemma π_grMap {C : Type u} [Category.{v} C] [Abelian C] {K L : FilteredObject C ℤᵒᵖ}
    (f : K ⟶ L) (p : ℤ) :
    cokernel.π (fstep K p) ≫ grMap f p = f.natTrans.app (op p) ≫ cokernel.π (fstep L p) :=
  cokernel.π_desc _ _ _

private lemma grToQuot_comp_quotStep (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) :
    grToQuot K p ≫ quotStep K p = 0 := by
  refine (cancel_epi (cokernel.π (fstep K p))).mp ?_
  rw [comp_zero, ← Category.assoc, π_grToQuot, Category.assoc, π_quotStep, cokernel.condition]

/-- The short exact sequence `0 → gr^p K → K/F^{p + 1} K → K/F^p K → 0`. -/
private noncomputable abbrev quotSeq (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk (grToQuot K p) (quotStep K p) (grToQuot_comp_quotStep K p)

/-- A morphism of filtered objects induces a morphism of the sequences
`0 → gr^p K → K/F^{p + 1} K → K/F^p K → 0`. -/
private noncomputable def quotSeqMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (p : ℤ) :
    quotSeq K p ⟶ quotSeq L p where
  τ₁ := grMap f p
  τ₂ := quotMap f (p + 1)
  τ₃ := quotMap f p
  comm₁₂ := by
    refine (cancel_epi (cokernel.π (fstep K p))).mp ?_
    rw [← Category.assoc, ← Category.assoc, π_grMap, π_grToQuot, Category.assoc, Category.assoc,
      π_grToQuot, π_quotMap, ← Category.assoc, ← Category.assoc, f.comm (op p)]
  comm₂₃ := by
    refine (cancel_epi (cokernel.π (K.filtration.ι.app (op (p + 1))))).mp ?_
    rw [← Category.assoc, ← Category.assoc, π_quotMap, π_quotStep, Category.assoc,
      π_quotStep, π_quotMap]

private lemma mono_grToQuot (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) : Mono (grToQuot K p) :=
  mono_cokernelMap_id_left (by rw [Category.id_comp]; exact fstep_comp_ι K p)

private lemma exact_quotSeq (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) : (quotSeq K p).Exact :=
  exact_cokernelComp (by rw [Category.id_comp]; exact fstep_comp_ι K p)
    (by rw [Category.comp_id]; exact (fstep_comp_ι K p).symm)

/-- The inductive heart of [Stacks, Tag 05QH] (4): if every `gr^p f` is a monomorphism and the
filtration of the source exhausts it at `r`, then every `K/F^p K ⟶ L/F^p L` is a monomorphism.
Below `r` the source quotient vanishes; above it the four lemma propagates monomorphy upwards
along the sequences `0 → gr^p → ·/F^{p + 1} → ·/F^p → 0`. -/
private lemma mono_quotMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (hgr : ∀ p : ℤ, Mono (grMap f p)) {r : ℤ} (hr : IsIso (K.filtration.ι.app (op r))) (p : ℤ) :
    Mono (quotMap f p) := by
  have hbase : ∀ q : ℤ, q ≤ r → Mono (quotMap f q) := by
    intro q hq
    have := Filtration.isIso_ι_app_of_le K.filtration hq hr
    have hz : IsZero (cokernel (K.filtration.ι.app (op q))) :=
      (Preadditive.epi_iff_isZero_cokernel _).mp inferInstance
    exact ⟨fun _ _ _ => hz.eq_of_tgt _ _⟩
  have hstep : ∀ q : ℤ, Mono (quotMap f q) → Mono (quotMap f (q + 1)) := by
    intro q hq
    have h₁ : Mono (quotSeqMap f q).τ₁ := hgr q
    have h₃ : Mono (quotSeqMap f q).τ₃ := hq
    have hK₁ : Mono (quotSeq K q).f := mono_grToQuot K q
    have hL₁ : Mono (quotSeq L q).f := mono_grToQuot L q
    exact ShortComplex.mono_τ₂_of_exact_of_mono (quotSeqMap f q) (exact_quotSeq K q)
  have hup : ∀ k : ℕ, Mono (quotMap f (r + (k : ℤ))) := by
    intro k
    induction k with
    | zero =>
        have e : r + ((0 : ℕ) : ℤ) = r := by simp
        rw [e]; exact hbase r le_rfl
    | succ k ih =>
        have e : r + ((k : ℤ) + 1) = r + (k : ℤ) + 1 := by ring
        rw [Nat.cast_succ, e]
        exact hstep _ ih
  by_cases hp : p ≤ r
  · exact hbase p hp
  · have hpr : r + ((p - r).toNat : ℤ) = p := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have h := hup (p - r).toNat
    rwa [hpr] at h

/-- **[Stacks, Tag 05QH] (4).** A morphism of filtered objects all of whose graded pieces are
monomorphisms, and whose source has finite filtration, is strict. -/
theorem isStrictHom_of_mono_grMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (hK : K.filtration.IsFinite) (hgr : ∀ p : ℤ, Mono (grMap f p)) : IsStrictHom f := by
  obtain ⟨r, hr⟩ := hK.exists_isIso_ι
  refine ⟨fun i => ?_⟩
  obtain ⟨p⟩ := i
  exact isPullback_of_mono_cokernel_map (f.comm (op p)).symm (mono_quotMap f hgr hr p)

/-! ### Graded pieces in a fixed degree -/

/-- Cokernels of complexes are computed termwise, so the graded pieces of the filtered object in
degree `n` are the terms in degree `n` of the graded pieces of the filtered complex. -/
noncomputable def grEvalIso (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    (grObj K p).X n ≅ grObj (evalFil K n) p :=
  PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) (fstep K p)

private lemma π_grEvalIso_inv (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    cokernel.π (fstep (evalFil K n) p) ≫ (grEvalIso K p n).inv =
      (cokernel.π (fstep K p)).f n := by
  rw [grEvalIso, PreservesCokernel.iso_inv]
  exact π_comp_cokernelComparison (fstep K p) (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)

lemma π_grEvalIso_hom (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    (cokernel.π (fstep K p)).f n ≫ (grEvalIso K p n).hom = cokernel.π (fstep (evalFil K n) p) :=
  (congrArg (fun x => x ≫ (grEvalIso K p n).hom) (π_grEvalIso_inv K p n).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun x => cokernel.π (fstep (evalFil K n) p) ≫ x)
        (Iso.inv_hom_id (grEvalIso K p n))).trans (Category.comp_id _)))

lemma epi_π_f (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    Epi ((cokernel.π (fstep K p)).f n) := by
  have h : Epi (cokernel.π (fstep (evalFil K n) p) ≫ (grEvalIso K p n).inv) := inferInstance
  exact π_grEvalIso_inv K p n ▸ h

private lemma π_grMap_eval {A B : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : A ⟶ B) (p n : ℤ) :
    cokernel.π (fstep (evalFil A n) p) ≫ grMap ((evalFunctor n).map α) p =
      (α.natTrans.app (op p)).f n ≫ cokernel.π (fstep (evalFil B n) p) :=
  π_grMap ((evalFunctor n).map α) p

/-- Taking the `p`-th graded piece commutes with taking the term in degree `n`. -/
lemma grEvalIso_hom_comp_grMap {A B : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : A ⟶ B) (p n : ℤ) :
    (grEvalIso A p n).hom ≫ grMap ((evalFunctor n).map α) p =
      (grMap α p).f n ≫ (grEvalIso B p n).hom := by
  have hπn : (cokernel.π (fstep A p)).f n ≫ (grMap α p).f n
      = (α.natTrans.app (op p)).f n ≫ (cokernel.π (fstep B p)).f n := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, π_grMap]
  have step₁ : (cokernel.π (fstep A p)).f n ≫
      ((grEvalIso A p n).hom ≫ grMap ((evalFunctor n).map α) p)
      = (α.natTrans.app (op p)).f n ≫ cokernel.π (fstep (evalFil B n) p) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ grMap ((evalFunctor n).map α) p) (π_grEvalIso_hom A p n)).trans
        (π_grMap_eval α p n))
  have step₂ : (cokernel.π (fstep A p)).f n ≫ ((grMap α p).f n ≫ (grEvalIso B p n).hom)
      = (α.natTrans.app (op p)).f n ≫ cokernel.π (fstep (evalFil B n) p) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ (grEvalIso B p n).hom) hπn).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun x => (α.natTrans.app (op p)).f n ≫ x) (π_grEvalIso_hom B p n))))
  have := epi_π_f A p n
  exact (cancel_epi ((cokernel.π (fstep A p)).f n)).mp (step₁.trans step₂.symm)

/-- Monomorphy of `gr^p` in degree `n` is monomorphy of `gr^p` of the degree `n` term. -/
lemma mono_grMap_evalFunctor_map {A B : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : A ⟶ B) (p n : ℤ) (h : Mono ((grMap α p).f n)) :
    Mono (grMap ((evalFunctor n).map α) p) := by
  rw [← mono_comp_iff_of_isIso (grEvalIso A p n).hom, grEvalIso_hom_comp_grMap]
  infer_instance

/-- If a filtered complex vanishes in degree `n` then so does each of its graded pieces: the step
`F^p K^n` of the filtration is a subobject of `K^n = 0`. -/
lemma isZero_grObj_X {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {n : ℤ}
    (hK : IsZero (K.X.X n)) (p : ℤ) : IsZero ((grObj K p).X n) := by
  have hsub : IsZero ((evalFil K n).filtration.obj (op p)) :=
    IsZero.of_mono ((evalFil K n).filtration.ι.app (op p)) hK
  have hepi : Epi (fstep (evalFil K n) p) := ⟨fun _ _ _ => hsub.eq_of_src _ _⟩
  exact IsZero.of_iso ((Preadditive.epi_iff_isZero_cokernel _).mp hepi) (grEvalIso K p n)

/-- **Homology, Lemma 05S1**, in the form in which the source's construction uses it. A
quasi-isomorphism from a complex concentrated in degree `0` into a complex vanishing in degree
`-1` is a monomorphism in degree `0`: the cycles of the source in degree `0` are all of `X^0`, the
cycles of the target inject into `Y^0`, and on cycles the map is the isomorphism induced on
homology. -/
public lemma mono_f_zero_of_quasiIso {X Y : CochainComplex 𝒜 ℤ} (φ : X ⟶ Y) [QuasiIso φ]
    (hX1 : IsZero (X.X 1)) (hXm : IsZero (X.X (-1))) (hYm : IsZero (Y.X (-1))) :
    Mono (φ.f 0) := by
  have h₁ : IsIso (X.iCycles 0) := X.isIso_iCycles 0 1 (by simp) (hX1.eq_of_tgt _ _)
  have h₂ : IsIso (X.homologyπ 0) := X.isIso_homologyπ (-1) 0 (by simp) (hXm.eq_of_src _ _)
  have h₃ : IsIso (Y.homologyπ 0) := Y.isIso_homologyπ (-1) 0 (by simp) (hYm.eq_of_src _ _)
  have h₄ : IsIso (HomologicalComplex.homologyMap φ 0) := inferInstance
  have h₅ : IsIso (HomologicalComplex.cyclesMap φ 0) := by
    have e : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ Y.homologyπ 0) := by
      rw [← HomologicalComplex.homologyπ_naturality]; infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.cyclesMap φ 0) (Y.homologyπ 0)
  have hm : Mono (X.iCycles 0 ≫ φ.f 0) := by
    rw [← HomologicalComplex.cyclesMap_i]; infer_instance
  exact (mono_comp_iff_of_isIso (X.iCycles 0) (φ.f 0)).mp hm

end CochainComplex.FilteredInjective.TermwiseSplit

end FilteredTermwiseSplit

end
