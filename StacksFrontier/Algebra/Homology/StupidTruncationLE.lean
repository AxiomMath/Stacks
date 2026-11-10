module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc

/-!
# The quotient stupid truncation `σ^{≤p}` and the triangles of the stupid filtration

For a cochain complex `K` the *stupid* (or *brutal*) truncation `σ^{≤p}K` keeps the terms of `K`
in degrees `≤ p` and replaces the others by zero. No kernels or cokernels are taken, so this is
not the canonical truncation `τ^{≤p}`. Because the differential of a cochain complex raises the
degree, the degrees that `σ^{≤p}` discards sit *above* the retained ones, and therefore
`σ^{≤p}K` is a **quotient** of `K`, not a subcomplex: there is a canonical projection
`K ⟶ σ^{≤p}K` and canonical projections `σ^{≤p}K ⟶ σ^{≤p-1}K` between successive truncations.
They form a *decreasing* tower

`K = σ^{≤M}K ⟶ ⋯ ⟶ σ^{≤1}K ⟶ σ^{≤0}K`

whose successive kernels are the single terms of `K`. Each step is a degreewise split short
exact sequence

`0 ⟶ (single p).obj (Kᵖ) ⟶ σ^{≤p}K ⟶ σ^{≤p-1}K ⟶ 0`

and hence, in the derived category, a distinguished triangle

`σ^{≤p}K ⟶ σ^{≤p-1}K ⟶ (Kᵖ)⟦1 - p⟧ ⟶ (σ^{≤p}K)⟦1⟧`.

That family of triangles is the *stupid filtration* of `K`.

## Main definitions

* `StacksDraft.StupidTruncation.descStupidTrunc`: the factorisation `K.stupidTrunc e ⟶ L` of a
  map `K ⟶ L` whose target is strictly supported on a truncation embedding `e` onto an initial
  segment: the universal property of `σ^{≤p}` as a quotient.
* `StacksDraft.StupidTruncation.stupidTruncLEMapLE`: the comparison `σ^{≤b}K ⟶ σ^{≤a}K` for
  `a ≤ b`.
* `StacksDraft.StupidTruncation.stupidTruncLETower`: the tower of quotient truncations
  `i ↦ σ^{≤-i}K`, a functor `ℤ ⥤ CochainComplex C ℤ`.
* `StacksDraft.StupidTruncation.stupidTruncLEι`: the inclusion of the top term
  `(single p).obj (Kᵖ) ⟶ σ^{≤p}K`.
* `StacksDraft.StupidTruncation.stupidTruncLEShortComplex`: the short complex
  `(single p).obj (Kᵖ) ⟶ σ^{≤p}K ⟶ σ^{≤p'}K`, for `p' + 1 = p`.
* `StacksDraft.StupidTruncation.stupidFiltration`: the tower `σ^{≤p}K` read in the derived
  category and indexed by `ℕ`.

## Main results

* `StacksDraft.StupidTruncation.stupidTruncLEShortComplex_shortExact`: the short complex above
  is short exact, being degreewise split.
* `StacksDraft.StupidTruncation.exists_distTriang_stupidTruncLE`: the distinguished triangle
  `σ^{≤p}K ⟶ σ^{≤p-1}K ⟶ (Kᵖ)⟦1 - p⟧ ⟶ (σ^{≤p}K)⟦1⟧` of the stupid filtration.
* `StacksDraft.StupidTruncation.exists_distTriang_stupidFiltration`: the same triangles indexed
  by `ℕ`.
* `StacksDraft.StupidTruncation.isIso_stupidTruncLEι`: for a complex concentrated in degrees
  `≥ p`, the truncation `σ^{≤p}K` *is* the single term `Kᵖ`.
* `StacksDraft.StupidTruncation.isIso_πStupidTruncLE`: for a complex concentrated in degrees
  `≤ p`, the projection `K ⟶ σ^{≤p}K` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace StacksDraft.StupidTruncation

universe w v u

/-! ### The universal property of the quotient truncation -/

section Projection

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c') (e : c.Embedding c')

open Classical in
/-- The degree-`i'` component of the factorisation `descStupidTrunc`: in a retained degree it is
the identification of terms followed by the given map, and the zero map into the zero object
otherwise. -/
noncomputable abbrev descStupidTruncf [e.IsRelIff] {L : HomologicalComplex A c'} (f : K ⟶ L)
    (i' : ι') : (K.stupidTrunc e).X i' ⟶ L.X i' :=
  if hi' : ∃ i, e.f i = i' then (K.stupidTruncXIso e hi'.choose_spec).hom ≫ f.f i' else 0

/-- In a retained degree, the component of the factorisation is the identification of terms
followed by the given map. -/
lemma descStupidTruncf_eq [e.IsRelIff] {L : HomologicalComplex A c'} (f : K ⟶ L)
    {i : ι} {i' : ι'} (hi' : e.f i = i') :
    descStupidTruncf K e f i' = (K.stupidTruncXIso e hi').hom ≫ f.f i' := by
  have h : ∃ k, e.f k = i' := ⟨i, hi'⟩
  have : h.choose = i := e.injective_f (by rw [h.choose_spec, hi'])
  grind

/-- The factorisation `K.stupidTrunc e ⟶ L` of a map `f : K ⟶ L` to a complex strictly supported
on `e`, where `e.IsTruncLE` places the degrees dropped by the truncation strictly above the
retained ones. -/
noncomputable def descStupidTrunc [e.IsTruncLE] {L : HomologicalComplex A c'}
    [L.IsStrictlySupported e] (f : K ⟶ L) : K.stupidTrunc e ⟶ L where
  f i' := descStupidTruncf K e f i'
  comm' i' j' hij' := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj'
      obtain ⟨i, hi⟩ := e.mem_prev (by rw [hj]; exact hij')
      rw [descStupidTruncf_eq K e f hi, descStupidTruncf_eq K e f hj,
        K.stupidTrunc_d_eq e hi hj]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.Hom.comm]
    · exact (L.isZero_X_of_isStrictlySupported e j' (by simpa using hj')).eq_of_tgt _ _

/-- In a retained degree, the factorisation is the identification of terms followed by the given
map. -/
lemma descStupidTrunc_f [e.IsTruncLE] {L : HomologicalComplex A c'} [L.IsStrictlySupported e]
    (f : K ⟶ L) {i : ι} {i' : ι'} (hi : e.f i = i') :
    (descStupidTrunc K e f).f i' = (K.stupidTruncXIso e hi).hom ≫ f.f i' :=
  descStupidTruncf_eq K e f hi

/-- In a retained degree, the projection `K ⟶ K.stupidTrunc e` is the inverse of the
identification of terms; in particular it is an isomorphism there. -/
lemma πStupidTrunc_f [e.IsTruncLE] {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.πStupidTrunc e).f i' = (K.stupidTruncXIso e hi).inv := by
  subst hi
  have key : (K.πStupidTrunc e).f (e.f i) =
      (K.restrictionXIso e (rfl : e.f i = e.f i)).inv ≫
        𝟙 ((K.restriction e).X i) ≫
          ((K.restriction e).extendXIso e (rfl : e.f i = e.f i)).inv :=
    e.liftExtend_f _ _ rfl
  rw [key, Category.id_comp]
  dsimp only [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
    Iso.trans_inv, eqToIso.inv]
  rfl

/-- The projection onto a stupid truncation along a truncation embedding onto an initial segment
is an epimorphism. -/
theorem epi_πStupidTrunc [e.IsTruncLE] : Epi (K.πStupidTrunc e) := by
  apply epi_of_epi_f
  intro i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    have := K.isIso_πStupidTrunc_f e hi
    infer_instance
  · exact ((K.stupidTrunc e).isZero_X_of_isStrictlySupported e i'
      (by simpa using hi')).epi _

end Projection

/-! ### The decreasing tower of quotient truncations -/

section Tower

open HomologicalComplex ComplexShape

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℤ)

/-- The degree `n ≤ a` is the image of `(a - n).toNat` under the embedding of the tower. -/
private theorem embeddingUpIntLE_f_toNat (a n : ℤ) (h : n ≤ a) :
    (embeddingUpIntLE a).f (a - n).toNat = n := by
  change a - ((a - n).toNat : ℤ) = n
  omega

/-- The term of `σ^{≤a}K` in a degree `n > a` is zero. -/
private theorem isZero_stupidTruncLE_X (a n : ℤ) (h : a < n) :
    IsZero ((K.stupidTrunc (embeddingUpIntLE a)).X n) :=
  CochainComplex.isZero_of_isStrictlyLE _ a n h

/-- In a retained degree `n ≤ a`, the term `(σ^{≤a}K)ⁿ` is identified with `Kⁿ`. -/
noncomputable abbrev stupidTruncLEXIso (a n : ℤ) (h : n ≤ a) :
    (K.stupidTrunc (embeddingUpIntLE a)).X n ≅ K.X n :=
  K.stupidTruncXIso (embeddingUpIntLE a) (i := (a - n).toNat)
    (by change a - ((a - n).toNat : ℤ) = n; omega)

/-- In a retained degree, the projection `K ⟶ σ^{≤a}K` is an isomorphism. -/
lemma isIso_πStupidTruncLE_f (a n : ℤ) (h : n ≤ a) :
    IsIso ((K.πStupidTrunc (embeddingUpIntLE a)).f n) :=
  K.isIso_πStupidTrunc_f _ (embeddingUpIntLE_f_toNat a n h)

/-- The comparison `σ^{≤b}K ⟶ σ^{≤a}K` for `a ≤ b`: the smaller truncation is strictly supported
in degrees `≤ b`, so the projection of `K` onto it factors through `σ^{≤b}K`. -/
noncomputable def stupidTruncLEMapLE {a b : ℤ} (h : a ≤ b) :
    K.stupidTrunc (embeddingUpIntLE b) ⟶ K.stupidTrunc (embeddingUpIntLE a) := by
  letI := CochainComplex.isStrictlyLE_of_le (K.stupidTrunc (embeddingUpIntLE a)) a b h
  exact descStupidTrunc K (embeddingUpIntLE b) (K.πStupidTrunc (embeddingUpIntLE a))

/-- The comparisons of the tower are compatible with the projections out of `K`. -/
lemma π_stupidTruncLEMapLE {a b : ℤ} (h : a ≤ b) :
    K.πStupidTrunc (embeddingUpIntLE b) ≫ stupidTruncLEMapLE K h =
      K.πStupidTrunc (embeddingUpIntLE a) := by
  ext n
  by_cases hn : n ≤ b
  · have hi := embeddingUpIntLE_f_toNat b n hn
    have := CochainComplex.isStrictlyLE_of_le (K.stupidTrunc (embeddingUpIntLE a)) a b h
    change (K.πStupidTrunc (embeddingUpIntLE b)).f n ≫
      (descStupidTrunc K (embeddingUpIntLE b) (K.πStupidTrunc (embeddingUpIntLE a))).f n = _
    rw [descStupidTrunc_f K (embeddingUpIntLE b) _ hi, πStupidTrunc_f K _ hi]
    simp
  · exact (isZero_stupidTruncLE_X K a n (by omega)).eq_of_tgt _ _

/-- In a degree retained by both truncations, the comparison `σ^{≤b}K ⟶ σ^{≤a}K` is the
composite of the two identifications with `Kⁿ`. -/
lemma stupidTruncLEMapLE_f {a b : ℤ} (h : a ≤ b) (n : ℤ) (hn : n ≤ a) :
    (stupidTruncLEMapLE K h).f n = (stupidTruncLEXIso K b n (hn.trans h)).hom ≫
      (stupidTruncLEXIso K a n hn).inv := by
  have := CochainComplex.isStrictlyLE_of_le (K.stupidTrunc (embeddingUpIntLE a)) a b h
  change (descStupidTrunc K (embeddingUpIntLE b)
    (K.πStupidTrunc (embeddingUpIntLE a))).f n = _
  rw [descStupidTrunc_f K (embeddingUpIntLE b) _ (embeddingUpIntLE_f_toNat b n (hn.trans h)),
    πStupidTrunc_f K _ (embeddingUpIntLE_f_toNat a n hn)]

/-- In a degree retained by both truncations, the comparison `σ^{≤b}K ⟶ σ^{≤a}K` is an
isomorphism. -/
lemma isIso_stupidTruncLEMapLE_f {a b : ℤ} (h : a ≤ b) (n : ℤ) (hn : n ≤ a) :
    IsIso ((stupidTruncLEMapLE K h).f n) := by
  rw [stupidTruncLEMapLE_f K h n hn]
  infer_instance

/-- The tower of quotient truncations `i ↦ σ^{≤-i}K`, whose term at `i` retains the degrees at
most `-i`, with the comparisons `stupidTruncLEMapLE` as transition maps. -/
noncomputable def stupidTruncLETower : ℤ ⥤ CochainComplex C ℤ where
  obj i := K.stupidTrunc (embeddingUpIntLE (-i))
  map f := stupidTruncLEMapLE K (neg_le_neg (leOfHom f))
  map_id i := by
    have := epi_πStupidTrunc K (embeddingUpIntLE (-i))
    apply (cancel_epi (K.πStupidTrunc (embeddingUpIntLE (-i)))).1
    simp only [π_stupidTruncLEMapLE, Category.comp_id]
  map_comp {i _ _} f g := by
    have := epi_πStupidTrunc K (embeddingUpIntLE (-i))
    apply (cancel_epi (K.πStupidTrunc (embeddingUpIntLE (-i)))).1
    simp only [← Category.assoc, π_stupidTruncLEMapLE]

/-- The inclusion `(single p).obj (Kᵖ) ⟶ σ^{≤p}K` of the top term of a quotient truncation. -/
noncomputable def stupidTruncLEι (p : ℤ) :
    (single C (.up ℤ) p).obj (K.X p) ⟶ K.stupidTrunc (embeddingUpIntLE p) :=
  mkHomFromSingle (stupidTruncLEXIso K p p le_rfl).inv (fun i hi ↦
    (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p)) p i
      (by change p + 1 = i at hi; omega)).eq_of_tgt _ _)

/-- The degree-`p` component of the inclusion of the top term. -/
lemma stupidTruncLEι_f (p : ℤ) :
    (stupidTruncLEι K p).f p = (singleObjXSelf (.up ℤ) p (K.X p)).hom ≫
      (stupidTruncLEXIso K p p le_rfl).inv :=
  mkHomFromSingle_f _ _

/-- The short complex `(single p).obj (Kᵖ) ⟶ σ^{≤p}K ⟶ σ^{≤p'}K`, for `p' + 1 = p`, exhibiting
the top term of a quotient truncation as the kernel of the next comparison. -/
noncomputable def stupidTruncLEShortComplex (p p' : ℤ) (hp : p' + 1 = p) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (stupidTruncLEι K p) (stupidTruncLEMapLE K (show p' ≤ p by omega))
    (by
      apply from_single_hom_ext
      exact (CochainComplex.isZero_of_isStrictlyLE
        (K.stupidTrunc (embeddingUpIntLE p')) p' p (by omega)).eq_of_tgt _ _)

/-- For a complex `K` concentrated in degrees `≥ p`, the inclusion `(single p).obj (Kᵖ) ⟶ σ^{≤p}K`
of the top term is an isomorphism. -/
instance isIso_stupidTruncLEι (p : ℤ) [K.IsStrictlyGE p] : IsIso (stupidTruncLEι K p) := by
  have : ∀ n : ℤ, IsIso ((stupidTruncLEι K p).f n) := by
    intro n
    by_cases hn : n = p
    · subst hn
      rw [stupidTruncLEι_f]
      infer_instance
    · refine IsZero.isIso (isZero_single_obj_X (.up ℤ) p (K.X p) n hn) ?_ _
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact (CochainComplex.isZero_of_isStrictlyGE K p n hlt).of_iso
          (stupidTruncLEXIso K p n hlt.le)
      · exact CochainComplex.isZero_of_isStrictlyLE
          (K.stupidTrunc (embeddingUpIntLE p)) p n hgt
  exact HomologicalComplex.Hom.isIso_of_components _

/-- For a complex `K` concentrated in degrees `≤ p`, the projection `K ⟶ σ^{≤p}K` is an
isomorphism. -/
instance isIso_πStupidTruncLE (p : ℤ) [K.IsStrictlyLE p] :
    IsIso (K.πStupidTrunc (embeddingUpIntLE p)) := by
  have : ∀ n : ℤ, IsIso ((K.πStupidTrunc (embeddingUpIntLE p)).f n) := by
    intro n
    by_cases hn : n ≤ p
    · exact isIso_πStupidTruncLE_f K p n hn
    · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyLE K p n (by omega))
        (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p)) p n
          (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

end Tower

/-! ### Short exactness -/

section ShortExact

open HomologicalComplex ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

/-- For `p' + 1 = p`, the sequence `0 ⟶ (single p).obj (Kᵖ) ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ 0` is short
exact. -/
lemma stupidTruncLEShortComplex_shortExact (p p' : ℤ) (hp : p' + 1 = p) :
    (stupidTruncLEShortComplex K p p' hp).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  let S := (stupidTruncLEShortComplex K p p' hp).map (eval C (.up ℤ) n)
  change S.ShortExact
  by_cases hn : n = p
  · subst n
    apply (ShortComplex.Splitting.ofIsIsoOfIsZero S ?_ ?_).shortExact
    · change IsIso ((stupidTruncLEι K p).f p)
      rw [stupidTruncLEι_f]
      infer_instance
    · exact isZero_stupidTruncLE_X K p' p (by omega)
  · apply (ShortComplex.Splitting.ofIsZeroOfIsIso S ?_ ?_).shortExact
    · exact isZero_single_obj_X (.up ℤ) p (K.X p) n hn
    · change IsIso ((stupidTruncLEMapLE K (show p' ≤ p by omega)).f n)
      by_cases hpn : n < p
      · exact isIso_stupidTruncLEMapLE_f K _ n (by omega)
      · exact IsZero.isIso
          (isZero_stupidTruncLE_X K p n (by omega))
          (isZero_stupidTruncLE_X K p' n (by omega)) _

end ShortExact

/-! ### The triangles of the stupid filtration -/

section Triangles

open HomologicalComplex ComplexShape DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℤ)

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Transporting a distinguished triangle along an isomorphism of its third object. -/
private lemma exists_distTriang_of_iso₃ {X Y Z Z' : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang D) (φ : Z ≅ Z') :
    ∃ (g' : Y ⟶ Z') (h' : Z' ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g' h' ∈ distTriang D :=
  ⟨g ≫ φ.hom, φ.inv ≫ h, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) φ.symm (by simp) (by simp) (by simp))⟩

/-- In the derived category, the shift by `1` of an object `X` placed in degree `p` is isomorphic
to the shift by `1 - p` of `X` placed in degree `0`. -/
noncomputable def singleShiftOneIso (X : C) (p : ℤ) :
    ((singleFunctor C p).obj X)⟦(1 : ℤ)⟧ ≅ ((singleFunctor C 0).obj X)⟦(1 - p : ℤ)⟧ :=
  (shiftFunctorAdd' (DerivedCategory C) p (1 - p) 1 (by omega)).app _ ≪≫
    (shiftFunctor (DerivedCategory C) (1 - p)).mapIso
      (((singleFunctors C).shiftIso p 0 p (add_zero p)).app X)

/-- For every cochain complex `K` and `p' + 1 = p` there is a distinguished triangle in the
derived category

`σ^{≤p}K ⟶ σ^{≤p'}K ⟶ (Kᵖ)⟦1 - p⟧ ⟶ (σ^{≤p}K)⟦1⟧`

whose first map is the comparison `stupidTruncLEMapLE`, where `Kᵖ` is read as a complex
concentrated in degree `0`. -/
theorem exists_distTriang_stupidTruncLE (p p' : ℤ) (hp : p' + 1 = p) :
    ∃ (g : Q.obj (K.stupidTrunc (embeddingUpIntLE p')) ⟶
        ((singleFunctor C 0).obj (K.X p))⟦(1 - p : ℤ)⟧)
      (h : ((singleFunctor C 0).obj (K.X p))⟦(1 - p : ℤ)⟧ ⟶
        (Q.obj (K.stupidTrunc (embeddingUpIntLE p)))⟦(1 : ℤ)⟧),
      Triangle.mk (Q.map (stupidTruncLEMapLE K (show p' ≤ p by omega))) g h ∈
        distTriang (DerivedCategory C) :=
  exists_distTriang_of_iso₃ _ _ _
    (rot_of_distTriang _ (triangleOfSES_distinguished
      (stupidTruncLEShortComplex_shortExact K p p' hp)))
    (singleShiftOneIso (K.X p) p)

/-- The stupid filtration of `K` read in the derived category and indexed by `ℕ`: the object at
`p` is `σ^{≤p}K`. -/
noncomputable def stupidFiltration (p : ℕ) : DerivedCategory C :=
  Q.obj (K.stupidTrunc (embeddingUpIntLE (p : ℤ)))

/-- The triangles of the stupid filtration, indexed by `ℕ`: for `0 < p` there is a distinguished
triangle

`σ^{≤p}K ⟶ σ^{≤p-1}K ⟶ (Kᵖ)⟦1 - p⟧ ⟶ (σ^{≤p}K)⟦1⟧`. -/
theorem exists_distTriang_stupidFiltration (p : ℕ) (hp : 0 < p) :
    ∃ (f : stupidFiltration K p ⟶ stupidFiltration K (p - 1))
      (g : stupidFiltration K (p - 1) ⟶ ((singleFunctor C 0).obj (K.X (p : ℤ)))⟦(1 - p : ℤ)⟧)
      (h : ((singleFunctor C 0).obj (K.X (p : ℤ)))⟦(1 - p : ℤ)⟧ ⟶
        (stupidFiltration K p)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory C) :=
  ⟨_, exists_distTriang_stupidTruncLE K (p : ℤ) ((p - 1 : ℕ) : ℤ) (by omega)⟩

end Triangles

end StacksDraft.StupidTruncation

end
