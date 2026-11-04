module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendUpNatIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechSummandAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCechFunctoriality

/-!
# The object of Tag 099E is the extended alternating Čech complex the tag displays

[Stacks, Tag 099E] displays the complex

`𝒪_U → ∏_{i₀} 𝒪_{U, f_{i₀}} → ∏_{i₀ < i₁} 𝒪_{U, f_{i₀} f_{i₁}} → ⋯ → 𝒪_{U, f_1 ⋯ f_r}`,

which is `AlgebraicGeometry.RingedSite.extendedAlternatingCech`: a complex of sheaves of
`𝒪`-modules, indexed by `ℤ`, whose degree-`p` term is a *product*, over the `p`-element subsets
`S` of `{1, …, r}`, of the sheaves `𝒪_{f_S}` obtained by inverting a subproduct. The object the
tag's *construction* produces is `AlgebraicGeometry.RingedSite.sheafifiedCech`: the
sheafification of the presheaf of complexes `V ↦ K(𝒪(V), (f_1|_V, …, f_r|_V))`, indexed by `ℕ`
and extended by zero, whose degree-`p` term is a *direct sum* over the same subsets of the
localizations of the ring of sections.

This file identifies the two. Both the indexing and the shape of the terms differ, and both
differences are resolved here:

* the direct sum over a finite index type is the product, which is what makes the degree-`p`
  terms agree — the inclusions and projections of
  `StacksFrontier/RingTheory/Cech/PresheafSummand.lean` exhibit the Čech term as the product of its
  summands, and the component formula for the Čech differential there is exactly the alternating
  differential of `CategoryTheory.AlternatingCech`;
* an `ℕ`-indexed complex extended by zero is a `ℤ`-indexed complex vanishing in negative
  degrees, which is `HomologicalComplex.extendUpNatIso`.

Sheafification then passes through the products, being additive and left exact
(`CategoryTheory.AlternatingCech.mapComplexIso`), and the sheafification of each summand is
`𝒪_{f_S}` (`AlgebraicGeometry.RingedSite.cechSummandFunctorSheafificationIso`).

## Main definitions

* `AlgebraicGeometry.RingedSite.cechPresheafTermIsoTerm`: the degree-`p` term of the presheaf of
  Čech complexes is the product of its summands.
* `AlgebraicGeometry.RingedSite.cechPresheafComplexIsoAlternating`: the presheaf of Čech
  complexes is the extended alternating Čech complex of the system of summands.
* `AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech`: **the object of
  [Stacks, Tag 099E] is the extended alternating Čech complex of the tag's display.**

## Main results

* `CategoryTheory.AlternatingCech.isZero_complex_X_of_neg`: the extended alternating Čech
  complex of any system vanishes in negative degrees, the index type being empty there.
* `AlgebraicGeometry.RingedSite.cechPresheafTermIsoTerm_comp_d`: the identification of the terms
  carries the Čech differential to the alternating differential.

## Implementation notes

The wrappers at the top of the `AlgebraicGeometry.RingedSite` section exist for the reason
recorded in the implementation notes of `SheafifiedCech.lean`: `(ringSheaf X).obj` and
`X.O.obj ⋙ forget₂ CommRingCat RingCat` are the same presheaf of rings only after
`CategoryTheory.sheafCompose` unfolds, which `rw` and `simp` will not do, so every statement
here is phrased in the first spelling and reaches the `Stacks.CechPresheaf` declarations only
through a `def` whose ascribed type is in that spelling.

The product decomposition is given as an explicit limit cone rather than through
`CategoryTheory.Limits.Bicone`: the bicone's `ι_π` field compares the two indices with a
dependent `if` and an `eqToHom`, whereas the two statements actually needed — the composite is
the identity at equal indices and zero at distinct ones — are available directly from
`DirectSum.component.lof_self` and `DirectSum.component.of`.

### Relation to the general case

For an arbitrary sheaf of ideals, [Stacks, Tag 099E] is
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech`, and [Stacks, Tag 099F] follows from it
as `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`. That construction sheafifies
on `𝒞` the presheaf of Čech complexes of *all* local generators of `ℐ` — a filtered colimit, so no
choice is made — and on each slice the leg into it from the Čech complex of one generating family
is locally bijective on homology; neither [Stacks, Tag 099D] nor any gluing is used. With the
identification below, the object of `SheafifiedCech.lean` is the complex the tag displays, and
`AlgebraicGeometry.RingedSite.exists_mem_sieve_iso_sheafifiedCech` is its independence of the
chosen generating family on the slices over a covering sieve.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]

/-- **The extended alternating Čech complex of a system vanishes in negative degrees**: there is
no subset of negative cardinality, so the term there is an empty product. -/
theorem isZero_complex_X_of_neg (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} (hp : p < 0) :
    IsZero ((complex F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  refine Pi.hom_ext _ _ fun b ↦ ?_
  exact (isEmpty_idx_of_neg hp).elim b

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

section Wrappers

/-- The degree-`p` term of the presheaf of Čech complexes. -/
def cechPresheafTerm (p : ℕ) :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  Stacks.CechPresheaf.cechPresheafTerm X.O.obj (cechFamily X f) (cechFamily_map X f) p

/-- The Čech differential of the presheaf of Čech complexes. -/
def cechPresheafDifferential (p : ℕ) :
    cechPresheafTerm X f p ⟶ cechPresheafTerm X f (p + 1) :=
  Stacks.CechPresheaf.cechPresheafDifferential X.O.obj (cechFamily X f) (cechFamily_map X f) p

/-- The presheaf of Čech complexes, indexed by `ℕ`. -/
def cechPresheafComplexNat :
    CochainComplex (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℕ :=
  Stacks.CechPresheaf.cechPresheafComplexNat X.O.obj (cechFamily X f) (cechFamily_map X f)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The `ℤ`-indexed presheaf of Čech complexes is the `ℕ`-indexed one extended by zero. -/
theorem cechPresheafComplex_eq_extend :
    cechPresheafComplex X f =
      (cechPresheafComplexNat X f).extend ComplexShape.embeddingUpNat :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The terms of the `ℕ`-indexed presheaf of Čech complexes. -/
theorem cechPresheafComplexNat_X (p : ℕ) :
    (cechPresheafComplexNat X f).X p = cechPresheafTerm X f p :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The differentials of the `ℕ`-indexed presheaf of Čech complexes. -/
theorem cechPresheafComplexNat_d (p : ℕ) :
    (cechPresheafComplexNat X f).d p (p + 1) = cechPresheafDifferential X f p :=
  CochainComplex.of_d _ _ _

/-- The inclusion of the summand indexed by `S` into the degree-`p` term. -/
def cechSummandInclusion (p : ℕ) (S : ExtendedAlternatingCech.Idx r p) :
    cechSummandPresheaf X f S.1 ⟶ cechPresheafTerm X f p :=
  Stacks.CechPresheaf.cechLocInclusion X.O.obj (cechFamily X f) (cechFamily_map X f) p S

/-- The projection of the degree-`p` term onto the summand indexed by `S`. -/
def cechSummandProjection (p : ℕ) (S : ExtendedAlternatingCech.Idx r p) :
    cechPresheafTerm X f p ⟶ cechSummandPresheaf X f S.1 :=
  Stacks.CechPresheaf.cechLocProjection X.O.obj (cechFamily X f) (cechFamily_map X f) p S

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The projection onto the summand indexed by `S` is a retraction of the inclusion of it. -/
theorem cechSummandInclusion_comp_cechSummandProjection_self (p : ℕ)
    (S : ExtendedAlternatingCech.Idx r p) :
    cechSummandInclusion X f p S ≫ cechSummandProjection X f p S = 𝟙 _ :=
  Stacks.CechPresheaf.cechLocInclusion_comp_cechLocProjection_self X.O.obj (cechFamily X f)
    (cechFamily_map X f) p S

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The inclusion of one summand followed by the projection onto a distinct one is zero. -/
theorem cechSummandInclusion_comp_cechSummandProjection_of_ne (p : ℕ)
    {S T : ExtendedAlternatingCech.Idx r p} (h : S ≠ T) :
    cechSummandInclusion X f p S ≫ cechSummandProjection X f p T = 0 :=
  Stacks.CechPresheaf.cechLocInclusion_comp_cechLocProjection_of_ne X.O.obj (cechFamily X f)
    (cechFamily_map X f) p h

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The idempotents cut out by the summands of the degree-`p` term sum to the identity. -/
theorem sum_cechSummandProjection_comp_cechSummandInclusion (p : ℕ) :
    ∑ S : ExtendedAlternatingCech.Idx r p,
        cechSummandProjection X f p S ≫ cechSummandInclusion X f p S =
      𝟙 (cechPresheafTerm X f p) :=
  Stacks.CechPresheaf.sum_cechLocProjection_comp_cechLocInclusion X.O.obj (cechFamily X f)
    (cechFamily_map X f) p

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The component formula for the Čech differential of the presheaf of Čech complexes.** -/
theorem cechPresheafDifferential_comp_cechSummandProjection (p : ℕ)
    (T : ExtendedAlternatingCech.Idx r (p + 1)) :
    cechPresheafDifferential X f p ≫ cechSummandProjection X f (p + 1) T =
      ∑ k : T.1, Cech.cechSign T.1 k.1 •
        (cechSummandProjection X f p (Cech.idxErase T k) ≫
          cechSummandTransition X f (Finset.erase_subset k.1 T.1)) :=
  Stacks.CechPresheaf.cechPresheafDifferential_comp_cechLocProjection X.O.obj (cechFamily X f)
    (cechFamily_map X f) p T

end Wrappers

section Product

/-- The index type of the degree-`p` term, in the `ℤ`-valued spelling the extended alternating
Čech complex uses and the `ℕ`-valued one the direct sum uses. -/
def cechIdxEquiv (p : ℕ) :
    AlternatingCech.Idx r (p : ℤ) ≃ ExtendedAlternatingCech.Idx r p where
  toFun S := ⟨S.1, by exact_mod_cast S.2⟩
  invFun S := ⟨S.1, by exact_mod_cast S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `cechIdxEquiv` does not change the underlying subset. -/
@[simp]
theorem cechIdxEquiv_val (p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    (cechIdxEquiv p S).1 = S.1 :=
  rfl

/-- The projection of the degree-`p` term onto the factor indexed by `S`, **with its type
written the way the extended alternating Čech complex writes it**. The two spellings of the
factor — the summand `cechSummandPresheaf X f S` and the value `(cechSummandFunctor X f).obj S`
of the system at `S` — agree only after a semireducible definition unfolds, which `rw` and
`simp` will not do, so the comparison below is phrased throughout in this one. -/
def cechTermProj (p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    cechPresheafTerm X f p ⟶ (cechSummandFunctor X f).obj S.1 :=
  cechSummandProjection X f p (cechIdxEquiv p S)

/-- The inclusion of the factor indexed by `S` into the degree-`p` term, in the same spelling. -/
def cechTermIncl (p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    (cechSummandFunctor X f).obj S.1 ⟶ cechPresheafTerm X f p :=
  cechSummandInclusion X f p (cechIdxEquiv p S)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The projection onto the factor indexed by `S` is a retraction of the inclusion of it. -/
theorem cechTermIncl_comp_cechTermProj_self (p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    cechTermIncl X f p S ≫ cechTermProj X f p S = 𝟙 _ :=
  cechSummandInclusion_comp_cechSummandProjection_self X f p (cechIdxEquiv p S)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The inclusion of one factor followed by the projection onto a distinct one is zero. -/
theorem cechTermIncl_comp_cechTermProj_of_ne (p : ℕ)
    {S T : AlternatingCech.Idx r (p : ℤ)} (h : S ≠ T) :
    cechTermIncl X f p S ≫ cechTermProj X f p T = 0 :=
  cechSummandInclusion_comp_cechSummandProjection_of_ne X f p fun he =>
    h ((cechIdxEquiv p).injective he)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The idempotents cut out by the factors of the degree-`p` term sum to the identity. -/
theorem sum_cechTermProj_comp_cechTermIncl (p : ℕ) :
    ∑ S : AlternatingCech.Idx r (p : ℤ), cechTermProj X f p S ≫ cechTermIncl X f p S =
      𝟙 (cechPresheafTerm X f p) := by
  rw [← sum_cechSummandProjection_comp_cechSummandInclusion X f p]
  exact Fintype.sum_equiv (cechIdxEquiv p) _
    (fun S => cechSummandProjection X f p S ≫ cechSummandInclusion X f p S) fun _ => rfl

/-- **The degree-`p` term of the presheaf of Čech complexes is the degree-`p` term of the
extended alternating Čech complex of the system of its summands.** The map into the product is
assembled from the projections onto the summands, and the map out of it from the inclusions. -/
def cechPresheafTermIsoTerm (p : ℕ) :
    cechPresheafTerm X f p ≅ AlternatingCech.term (cechSummandFunctor X f) (p : ℤ) where
  hom := Pi.lift (cechTermProj X f p)
  inv := ∑ S : AlternatingCech.Idx r (p : ℤ),
    Pi.π (fun T : AlternatingCech.Idx r (p : ℤ) => (cechSummandFunctor X f).obj T.1) S ≫
      cechTermIncl X f p S
  hom_inv_id := by
    rw [Preadditive.comp_sum, ← sum_cechTermProj_comp_cechTermIncl X f p]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Category.assoc, Pi.lift_π]
  inv_hom_id := by
    refine Pi.hom_ext _ _ fun T => ?_
    rw [Category.assoc, Pi.lift_π, Category.id_comp, Preadditive.sum_comp]
    refine (Finset.sum_eq_single_of_mem T (Finset.mem_univ T) fun S _ hST => ?_).trans ?_
    · rw [Category.assoc, cechTermIncl_comp_cechTermProj_of_ne X f p hST, comp_zero]
    · rw [Category.assoc, cechTermIncl_comp_cechTermProj_self, Category.comp_id]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The component of `cechPresheafTermIsoTerm` at `S` is the projection onto the factor `S`. -/
@[simp]
theorem cechPresheafTermIsoTerm_hom_comp_pi (p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    (cechPresheafTermIsoTerm X f p).hom ≫
        Pi.π (fun T : AlternatingCech.Idx r (p : ℤ) =>
          (cechSummandFunctor X f).obj T.1) S =
      cechTermProj X f p S :=
  Pi.lift_π _ _

/-- A subset of cardinality `p + 1`, with its cardinality read as `(p : ℤ) + 1` rather than as
`((p + 1 : ℕ) : ℤ)`. The two agree, but only definitionally, and the alternating differential out
of degree `p` lands in the first while the degree-`(p + 1)` term of the `ℕ`-indexed complex is
indexed by the second; this names the passage so that no statement below has to cross it. -/
def cechIdxSucc (p : ℕ) (T : AlternatingCech.Idx r ((p : ℤ) + 1)) :
    AlternatingCech.Idx r ((p + 1 : ℕ) : ℤ) :=
  ⟨T.1, by push_cast; exact T.2⟩

/-- `cechIdxSucc` does not change the underlying subset. -/
@[simp]
theorem cechIdxSucc_val (p : ℕ) (T : AlternatingCech.Idx r ((p : ℤ) + 1)) :
    (cechIdxSucc p T).1 = T.1 :=
  rfl

/-- The identification of the degree-`(p + 1)` term, with its target written at the degree the
alternating differential out of degree `p` lands in. It is the same isomorphism; only the
spelling of the degree differs, and the two spellings agree definitionally but not
syntactically, which is what would otherwise stop every rewrite below. -/
def cechPresheafTermIsoTermSucc (p : ℕ) :
    cechPresheafTerm X f (p + 1) ≅
      AlternatingCech.term (cechSummandFunctor X f) ((p : ℤ) + 1) :=
  cechPresheafTermIsoTerm X f (p + 1)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The same as `cechPresheafTermIsoTerm_hom_comp_pi`, in degree `p + 1` and at the index type
the alternating differential out of degree `p` lands in. -/
theorem cechPresheafTermIsoTermSucc_hom_comp_pi (p : ℕ)
    (S : AlternatingCech.Idx r ((p : ℤ) + 1)) :
    (cechPresheafTermIsoTermSucc X f p).hom ≫
        Pi.π (fun T : AlternatingCech.Idx r ((p : ℤ) + 1) =>
          (cechSummandFunctor X f).obj T.1) S =
      cechTermProj X f (p + 1) (cechIdxSucc p S) :=
  Pi.lift_π _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The component formula for the Čech differential**, in the spelling the alternating
differential uses: its component at a subset `T` of cardinality `p + 1` is the alternating sum,
over the elements `k` of `T`, of the projections onto the factors indexed by `T ∖ k` followed by
the transition maps of the system into the factor indexed by `T`. -/
theorem cechPresheafDifferential_comp_cechTermProj (p : ℕ)
    (T : AlternatingCech.Idx r ((p : ℤ) + 1)) :
    cechPresheafDifferential X f p ≫ cechTermProj X f (p + 1) (cechIdxSucc p T) =
      ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
        (cechTermProj X f p (AlternatingCech.Idx.erase T k) ≫
          (cechSummandFunctor X f).map (homOfLE (AlternatingCech.Idx.erase_subset T k))) := by
  rw [← Finset.univ_eq_attach]
  exact cechPresheafDifferential_comp_cechSummandProjection X f p
    (cechIdxEquiv (p + 1) (cechIdxSucc p T))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The identification of the terms carries the Čech differential to the alternating
differential.** -/
theorem cechPresheafTermIsoTerm_comp_d (p : ℕ) :
    (cechPresheafTermIsoTerm X f p).hom ≫
        (AlternatingCech.complex (cechSummandFunctor X f)).d (p : ℤ) ((p : ℤ) + 1) =
      cechPresheafDifferential X f p ≫ (cechPresheafTermIsoTermSucc X f p).hom := by
  have hd : (AlternatingCech.complex (cechSummandFunctor X f)).d (p : ℤ) ((p : ℤ) + 1) =
      AlternatingCech.d (cechSummandFunctor X f) (p : ℤ) :=
    AlternatingCech.complex_d _ _
  rw [hd]
  refine Pi.hom_ext _ _ fun T => ?_
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  rw [cechPresheafTermIsoTermSucc_hom_comp_pi]
  refine Eq.trans ?_ (cechPresheafDifferential_comp_cechTermProj X f p T).symm
  rw [AlternatingCech.d_comp_pi, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (Preadditive.comp_zsmul _ _ _).trans
    (congrArg (fun m => Cech.cechSign T.1 k.1 • m) ?_)
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ (cechSummandFunctor X f).map
        (homOfLE (AlternatingCech.Idx.erase_subset T k)))
      (cechPresheafTermIsoTerm_hom_comp_pi X f p (AlternatingCech.Idx.erase T k)))

end Product

section Complex

/-- The identification of the degree-`n` terms, with the target degree given as an integer `p`
equal to `n`. -/
def cechTermIso (n : ℕ) (p : ℤ) (hnp : (n : ℤ) = p) :
    ((cechPresheafComplexNat X f).X n ≅
      (AlternatingCech.complex (cechSummandFunctor X f)).X p) :=
  hnp ▸ cechPresheafTermIsoTerm X f n

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- At `p = n`, `cechTermIso` is `cechPresheafTermIsoTerm`. -/
theorem cechTermIso_self (n : ℕ) :
    cechTermIso X f n (n : ℤ) rfl = cechPresheafTermIsoTerm X f n :=
  rfl

/-- **The presheaf of Čech complexes is the extended alternating Čech complex of the system of
its summands.** -/
def cechPresheafComplexIsoAlternating :
    cechPresheafComplex X f ≅ AlternatingCech.complex (cechSummandFunctor X f) :=
  HomologicalComplex.extendUpNatIso (cechPresheafComplexNat X f)
    (AlternatingCech.complex (cechSummandFunctor X f))
    (fun _ hp => AlternatingCech.isZero_complex_X_of_neg _ hp) (cechTermIso X f)
    (fun n p q hp hq => by
      subst hp
      subst hq
      rw [cechTermIso_self, cechTermIso_self, cechPresheafComplexNat_d]
      exact cechPresheafTermIsoTerm_comp_d X f n)

/-- **The object of [Stacks, Tag 099E] is the extended alternating Čech complex the tag
displays.** The sheafification of the presheaf of Čech complexes of a finite family of global
sections of `𝒪` is the complex

`𝒪 → ∏_{i₀} 𝒪_{f_{i₀}} → ∏_{i₀ < i₁} 𝒪_{f_{i₀} f_{i₁}} → ⋯ → 𝒪_{f_1 ⋯ f_r}`

of sheaves of `𝒪`-modules. -/
def sheafifiedCechIsoExtendedAlternatingCech :
    sheafifiedCech X f ≅ extendedAlternatingCech X f :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (cechPresheafComplexIsoAlternating X f) ≪≫
    AlternatingCech.mapComplexIso (moduleSheafificationFunctor X) (cechSummandFunctor X f) ≪≫
    AlternatingCech.complexMapIso (cechSummandFunctorSheafificationIso X f)

end Complex

end AlgebraicGeometry.RingedSite

end
