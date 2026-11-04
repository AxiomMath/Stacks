module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.Algebra.Homology.MapExtendComplex
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Applying a complex of functors to a complex

Let `H` be a cochain complex of functors `C ⥤ D` indexed by `ℕ` and let `F` be a cochain
complex of `C` indexed by `ℤ`. Applying `H^n` termwise to `F` and letting `n` vary produces a
cochain complex of cochain complexes,

```
(n, p) ↦ H^n(F^p),
```

which is `HomologicalComplex.liftComplexOfFunctors`. The construction is functorial in `H` and
sends homotopies to homotopies (`liftComplexOfFunctorsHomotopy`), hence homotopy equivalences to
homotopy equivalences (`liftComplexOfFunctorsHomotopyEquiv`); composing with the extension of the
outer index from `ℕ` to `ℤ` gives `liftComplexOfFunctorsExtendHomotopyEquiv`, a homotopy
equivalence of double complexes indexed by `ℤ` in both directions.

This is the shape in which a *degreewise* resolution of a complex is compared with the complex
itself: the complex of functors is a resolution of the identity, and the comparison of double
complexes is then totalised.

## Main definitions

* `HomologicalComplex.liftComplexOfFunctors`: the double complex `(n, p) ↦ H^n(F^p)`.
* `HomologicalComplex.liftComplexOfFunctorsMap`,
  `HomologicalComplex.liftComplexOfFunctorsHomotopy`,
  `HomologicalComplex.liftComplexOfFunctorsHomotopyEquiv`: functoriality in `H`, and its
  compatibility with homotopies.
* `HomologicalComplex.extendHomotopyEquiv`: the extension of a homotopy equivalence along an
  embedding of complex shapes, with the extension of the forward map as forward map.
* `HomologicalComplex.liftFunctorToComplex`: the same construction for a functor
  `P : C ⥤ CochainComplex D ℕ` rather than a complex of functors, together with
  `HomologicalComplex.liftComplexOfFunctorsIso` comparing the two when `H.asFunctor ≅ P`.
* `HomologicalComplex.liftFunctorToComplexSingleIso`: the lift of the functor `A ↦ S(A)[0]` is
  the complex `S(F)` placed in degree `0`.

## Main results

* `HomologicalComplex.exactAt_and_isIso_kernelLift_of_quasiIso_single`: a quasi-isomorphism from
  a complex concentrated in degree `0` exhibits its target as a resolution -- exact away from
  `0`, with the kernel of its first differential the given object.
* `HomologicalComplex.preservesZeroMorphisms_of_eval_iso`,
  `HomologicalComplex.preservesZeroMorphisms_X_of_asFunctor_iso`: the two ways of recognising
  that a complex-valued functor, resp. each term of a complex of functors, preserves zero
  morphisms.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

universe v v' u u'

/-! ### Preserving zero morphisms -/

/-- A complex-valued functor preserves zero morphisms as soon as each of its terms is isomorphic
to a functor that does -- in the application, to an iterate of a functor. -/
lemma preservesZeroMorphisms_of_eval_iso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject D]
    (G : C ⥤ CochainComplex D ℕ) (T : ℕ → (C ⥤ D))
    (h : ∀ n : ℕ, G ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n ≅ T n)
    (hT : ∀ n : ℕ, (T n).PreservesZeroMorphisms) :
    G.PreservesZeroMorphisms := by
  refine ⟨fun M N => HomologicalComplex.hom_ext _ _ fun n => ?_⟩
  have := hT n
  have hn : (G ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).map (0 : M ⟶ N) = 0 :=
    (cancel_mono ((h n).hom.app N)).1 (by simpa using (h n).hom.naturality (0 : M ⟶ N))
  simpa using hn

/-- Each term of a complex of functors preserves zero morphisms as soon as the associated
functor to complexes is isomorphic to one whose terms do. -/
lemma preservesZeroMorphisms_X_of_asFunctor_iso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (H : CochainComplex (C ⥤ D) ℕ) (P : C ⥤ CochainComplex D ℕ)
    (e : H.asFunctor ≅ P)
    (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms) :
    ∀ n, (H.X n).PreservesZeroMorphisms := by
  intro n
  have := hP n
  exact Functor.preservesZeroMorphisms_of_iso
    (F₁ := P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n)
    (NatIso.ofComponents (fun A => HomologicalComplex.Hom.isoApp (e.app A).symm n)
      fun f => congrArg (fun φ => φ.f n) (e.inv.naturality f))

/-- Postcomposing the complex concentrated in a single degree `i` with an additive functor
preserves zero morphisms in every degree: isomorphic to the functor itself in degree `i` (via
`singleObjXSelf`, carried across `S.map` and using that `single` already preserves zero
morphisms), and trivially preserving zero morphisms elsewhere, every object there being sent to a
zero object. -/
lemma preservesZeroMorphisms_single_mapHomologicalComplex_eval
    {C D : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [Category D] [Preadditive D] [HasZeroObject D]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (i : ι) (S : C ⥤ D) [S.Additive] (n : ι) :
    ((HomologicalComplex.single C c i ⋙ S.mapHomologicalComplex c) ⋙
      HomologicalComplex.eval D c n).PreservesZeroMorphisms := by
  by_cases h : n = i
  · subst n
    refine ⟨fun A B => ?_⟩
    show S.map (((HomologicalComplex.single C c i).map (0 : A ⟶ B)).f i) = 0
    simp
  · exact ⟨fun M N => (S.map_isZero
      (HomologicalComplex.isZero_single_obj_X c i M n h)).eq_of_src _ _⟩

/-- Postcomposing a complex-valued functor with an additive functor, then evaluating in a degree,
preserves zero morphisms as soon as evaluating the original functor in that degree does: the two
orders of composition -- apply the additive functor termwise then evaluate, or evaluate then
apply the additive functor -- agree definitionally. -/
lemma preservesZeroMorphisms_mapHomologicalComplex_comp_eval
    {C D D' : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category D'] [Preadditive D']
    (Q : C ⥤ CochainComplex D ℕ) (n : ℕ)
    [(Q ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms]
    (T : D ⥤ D') [T.Additive] :
    ((Q ⋙ T.mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
      HomologicalComplex.eval D' (ComplexShape.up ℕ) n).PreservesZeroMorphisms :=
  inferInstanceAs
    (((Q ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n) ⋙ T).PreservesZeroMorphisms)

/-! ### A complex of functors applied to a complex -/

section Preadditive

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]

/-- **A complex of functors applied to a complex**: the double complex `(n, p) ↦ H^n(F^p)`, with
the differential of `H` in the outer (`ℕ`-indexed) direction and the differential of `F` in the
inner one. -/
noncomputable def liftComplexOfFunctors
    (H : CochainComplex (C ⥤ D) ℕ)
    (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) : CochainComplex (CochainComplex D ℤ) ℕ where
  X n := by
    letI := hH n
    exact ((H.X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  d n n' :=
    { f p := (H.d n n').app (F.X p)
      comm' := by
        intro p q _
        exact ((H.d n n').naturality (F.d p q)).symm }
  shape n n' h := by
    ext p
    exact congrArg (fun α => α.app (F.X p)) (H.shape n n' h)
  d_comp_d' n n' n'' _ _ := by
    ext p
    change (H.d n n').app (F.X p) ≫ (H.d n' n'').app (F.X p) = 0
    simpa only [NatTrans.comp_app, NatTrans.app_zero] using
      congrArg (fun α => α.app (F.X p)) (H.d_comp_d n n' n'')

/-- `liftComplexOfFunctors` is functorial in the complex of functors. -/
noncomputable def liftComplexOfFunctorsMap
    {H H' : CochainComplex (C ⥤ D) ℕ} (α : H ⟶ H')
    (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (hH' : ∀ n, (H'.X n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) : liftComplexOfFunctors H hH F ⟶
      liftComplexOfFunctors H' hH' F where
  f n :=
    { f p := (α.f n).app (F.X p)
      comm' := by
        intro p q _
        exact ((α.f n).naturality (F.d p q)).symm }
  comm' n n' _ := by
    ext p
    exact congrArg (fun τ => τ.app (F.X p)) (α.comm n n')

/-- The components of `liftComplexOfFunctorsMap`: the natural transformation evaluated at the
term of the complex. -/
lemma liftComplexOfFunctorsMap_f_f
    {H H' : CochainComplex (C ⥤ D) ℕ} (α : H ⟶ H')
    (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (hH' : ∀ n, (H'.X n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) (n : ℕ) (p : ℤ) :
    ((liftComplexOfFunctorsMap α hH hH' F).f n).f p = (α.f n).app (F.X p) :=
  rfl

/-- A homotopy between morphisms of complexes of functors induces a homotopy between the
morphisms they induce on the lifts. -/
noncomputable def liftComplexOfFunctorsHomotopy
    {H H' : CochainComplex (C ⥤ D) ℕ} {f g : H ⟶ H'} (h : Homotopy f g)
    (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (hH' : ∀ n, (H'.X n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) :
    Homotopy (liftComplexOfFunctorsMap f hH hH' F)
      (liftComplexOfFunctorsMap g hH hH' F) where
  hom n n' :=
    { f p := (h.hom n n').app (F.X p)
      comm' := by
        intro p q _
        exact ((h.hom n n').naturality (F.d p q)).symm }
  zero n n' hn := by
    ext p
    exact congrArg (fun τ => τ.app (F.X p)) (h.zero n n' hn)
  comm n := by
    apply HomologicalComplex.hom_ext
    intro p
    change (f.f n).app (F.X p) =
      (H.d n ((ComplexShape.up ℕ).next n)).app (F.X p) ≫
          (h.hom ((ComplexShape.up ℕ).next n) n).app (F.X p) +
        (h.hom n ((ComplexShape.up ℕ).prev n)).app (F.X p) ≫
          (H'.d ((ComplexShape.up ℕ).prev n) n).app (F.X p) +
        (g.f n).app (F.X p)
    exact congrArg (fun τ => τ.app (F.X p)) (h.comm n)

/-- A homotopy equivalence of complexes of functors induces a homotopy equivalence of the
lifts. -/
noncomputable def liftComplexOfFunctorsHomotopyEquiv [HasZeroObject D]
    {H H' : CochainComplex (C ⥤ D) ℕ} (e : HomotopyEquiv H H')
    (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (hH' : ∀ n, (H'.X n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) :
    HomotopyEquiv (liftComplexOfFunctors H hH F)
      (liftComplexOfFunctors H' hH' F) where
  hom := liftComplexOfFunctorsMap e.hom hH hH' F
  inv := liftComplexOfFunctorsMap e.inv hH' hH F
  homotopyHomInvId := liftComplexOfFunctorsHomotopy e.homotopyHomInvId hH hH F
  homotopyInvHomId := liftComplexOfFunctorsHomotopy e.homotopyInvHomId hH' hH' F

end Preadditive

/-! ### Extending a homotopy equivalence along an embedding of shapes -/

section ExtendHomotopyEquiv

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {Z Z' : HomologicalComplex A c} (e : HomotopyEquiv Z Z') (emb : c.Embedding c')
  [emb.IsRelIff]

/-- **A homotopy equivalence of complexes extends along an embedding of complex shapes.** The
forward map of the extension is the extension of the forward map, which is
`extendHomotopyEquiv_hom`; that is what makes the extension usable in a computation, the
homotopy inverse being supplied by `homotopyEquivalences_extendMap_iff` and therefore only
available through a choice. -/
noncomputable def extendHomotopyEquiv :
    HomotopyEquiv (Z.extend emb) (Z'.extend emb) :=
  (Classical.choose
      ((homotopyEquivalences_extendMap_iff e.hom emb).2 e.homotopyEquivalences_hom)).copy
    (Homotopy.ofEq (Classical.choose_spec
      ((homotopyEquivalences_extendMap_iff e.hom emb).2 e.homotopyEquivalences_hom)))

/-- The forward map of `extendHomotopyEquiv` is the extension of the forward map. -/
lemma extendHomotopyEquiv_hom :
    (extendHomotopyEquiv e emb).hom = extendMap e.hom emb := rfl

end ExtendHomotopyEquiv

section Preadditive2

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]

/-- **A complex-valued functor applied to a complex**: the same double complex as
`liftComplexOfFunctors`, but for a functor `P : C ⥤ CochainComplex D ℕ`, which keeps the complex
direction of `P` visible. -/
noncomputable def liftFunctorToComplex
    (P : C ⥤ CochainComplex D ℕ)
    (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) :
    CochainComplex (CochainComplex D ℤ) ℕ where
  X n := by
    letI := hP n
    exact ((P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n)
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  d n n' :=
    { f q := (P.obj (F.X q)).d n n'
      comm' := by
        intro q q' _
        exact ((P.map (F.d q q')).comm n n').symm }
  shape n n' h := by
    ext q
    exact (P.obj (F.X q)).shape n n' h
  d_comp_d' n n' n'' _ _ := by
    ext q
    exact (P.obj (F.X q)).d_comp_d n n' n''

/-- An isomorphism between the functor associated with a complex of functors and a
complex-valued functor identifies the two lifts. -/
noncomputable def liftComplexOfFunctorsIso
    {H : CochainComplex (C ⥤ D) ℕ} (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (P : C ⥤ CochainComplex D ℕ)
    (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (i : H.asFunctor ≅ P)
    (F : CochainComplex C ℤ) :
    liftComplexOfFunctors H hH F ≅ liftFunctorToComplex P hP F := by
  apply HomologicalComplex.Hom.isoOfComponents
    (fun n => HomologicalComplex.Hom.isoOfComponents
      (fun q => (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n :
        (H.X n).obj (F.X q) ≅ (P.obj (F.X q)).X n))
      (by
        intro q q' _
        have hnat := i.hom.naturality (F.d q q')
        change (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n).hom ≫
            (P.map (F.d q q')).f n =
          (H.X n).map (F.d q q') ≫
            (HomologicalComplex.Hom.isoApp (i.app (F.X q')) n).hom
        exact congrArg (fun f => f.f n) hnat.symm))
    (by
      intro n n' _
      ext q
      change (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n).hom ≫
          (P.obj (F.X q)).d n n' =
        (H.d n n').app (F.X q) ≫
          (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n').hom
      exact (i.app (F.X q)).hom.comm n n')

/-- The components of `liftComplexOfFunctorsIso`: the isomorphism of complexes of functors
evaluated at the term of the complex. -/
lemma liftComplexOfFunctorsIso_hom_f_f
    {H : CochainComplex (C ⥤ D) ℕ} (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (P : C ⥤ CochainComplex D ℕ)
    (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (i : H.asFunctor ≅ P) (F : CochainComplex C ℤ) (n : ℕ) (q : ℤ) :
    (((liftComplexOfFunctorsIso hH P hP i F).hom.f n).f q) =
      (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n).hom :=
  rfl

/-- **A complex-valued functor applied to a complex, then pushed forward termwise, is the same
double complex as the lift of the composite functor.**
`liftFunctorToComplex (Q ⋙ T.mapHomologicalComplex c) hP F` and
`mapBicomplex T (liftFunctorToComplex Q hQ F)` are the same double complex `(n, q) ↦ T(Q(F^q)^n)`,
reached by applying `T` before or after lifting `Q` along `F`. This is what lets a homotopy
equivalence of complexes of functors, once lifted along `F` and extended to `ℤ`, be compared with
the double complex obtained by applying an additive functor termwise to a *different*
presentation of the same lift (`liftFunctorToComplexExtend`). -/
noncomputable def liftFunctorToComplexMapIso
    {D' : Type*} [Category D'] [Preadditive D']
    (Q : C ⥤ CochainComplex D' ℕ)
    (hQ : ∀ n, (Q ⋙ HomologicalComplex.eval D' (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (T : D' ⥤ D) [T.Additive]
    (hP : ∀ n, ((Q ⋙ T.mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
      HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) :
    liftFunctorToComplex (Q ⋙ T.mapHomologicalComplex (ComplexShape.up ℕ)) hP F ≅
      HomologicalComplex₂.TotalMap.mapBicomplex T (liftFunctorToComplex Q hQ F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => HomologicalComplex.Hom.isoOfComponents
      (fun q => Iso.refl _)
      (by intro q q' _; simp [liftFunctorToComplex]))
    (by
      intro n n' _
      ext q
      simp [liftFunctorToComplex, HomologicalComplex₂.TotalMap.mapBicomplex,
        Functor.mapHomologicalComplex])

/-- The components of the inverse of `liftComplexOfFunctorsIso`. -/
lemma liftComplexOfFunctorsIso_inv_f_f
    {H : CochainComplex (C ⥤ D) ℕ} (hH : ∀ n, (H.X n).PreservesZeroMorphisms)
    (P : C ⥤ CochainComplex D ℕ)
    (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (i : H.asFunctor ≅ P) (F : CochainComplex C ℤ) (n : ℕ) (q : ℤ) :
    (((liftComplexOfFunctorsIso hH P hP i F).inv.f n).f q) =
      (HomologicalComplex.Hom.isoApp (i.app (F.X q)) n).inv :=
  rfl

/-- **The lift of `A ↦ S(A)[0]` is `S(F)[0]`**: applying the complex-valued functor that places
`S(A)` in degree `0` to every term of `F` gives the complex `S(F)` in outer degree `0`. -/
noncomputable def liftFunctorToComplexSingleIso [HasZeroObject C] [HasZeroObject D]
    (S : C ⥤ D) [S.PreservesZeroMorphisms]
    (hP : ∀ n, ((CochainComplex.single₀ C ⋙ S.mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
      HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) :
    liftFunctorToComplex
      (CochainComplex.single₀ C ⋙ S.mapHomologicalComplex (ComplexShape.up ℕ)) hP F ≅
        (CochainComplex.single₀ (CochainComplex D ℤ)).obj
          ((S.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) := by
  let K := liftFunctorToComplex
    (CochainComplex.single₀ C ⋙ S.mapHomologicalComplex (ComplexShape.up ℕ)) hP F
  let M := (S.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have hz (n : ℕ) (hn : n ≠ 0) : IsZero (K.X n) := by
    rw [IsZero.iff_id_eq_zero]
    ext p
    exact (S.map_isZero (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (F.X p) n hn)).eq_of_src _ _
  let e₀ : K.X 0 ≅ M := HomologicalComplex.Hom.isoOfComponents
    (fun _ => Iso.refl _) (by
      intro p q _
      simp [K, M, liftFunctorToComplex])
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n => if h : n = 0 then by subst n; exact e₀
      else IsZero.iso (hz n h)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 M n h))
    (by
      intro n n' h
      by_cases hn : n = 0
      · subst n
        have hn' : n' ≠ 0 := by
          have h' : 0 + 1 = n' := h
          omega
        exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℕ) 0 M n' hn').eq_of_tgt _ _
      · exact (hz n hn).eq_of_src _ _)

/-- The inverse of `liftFunctorToComplexSingleIso` is, in outer degree `0`, the identity in every
inner degree. -/
lemma liftFunctorToComplexSingleIso_inv_f_zero_f [HasZeroObject C] [HasZeroObject D]
    (S : C ⥤ D) [S.PreservesZeroMorphisms]
    (hP : ∀ n, ((CochainComplex.single₀ C ⋙ S.mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
      HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
    (F : CochainComplex C ℤ) (q : ℤ) :
    ((liftFunctorToComplexSingleIso S hP F).inv.f 0).f q = 𝟙 _ := by
  simp only [liftFunctorToComplexSingleIso, HomologicalComplex.Hom.isoOfComponents]
  rfl

/-! ### The associated double complex indexed by `ℤ` in both directions -/

section Extend

variable [HasZeroObject D]
  (P : C ⥤ CochainComplex D ℕ)
  (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
  (F : CochainComplex C ℤ)

/-- **The double complex of a complex-valued functor applied to a complex**: the double complex
`(p, q) ↦ (P(F^q))^p` of `liftFunctorToComplex`, with its outer index extended from `ℕ` to `ℤ`
by zero. This is the shape to which [Stacks, Tag 0133] and [Stacks, Tag 0FKH] apply. -/
noncomputable abbrev liftFunctorToComplexExtend :
    HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (liftFunctorToComplex P hP F).extend ComplexShape.embeddingUpNat

omit [HasZeroObject D] in
/-- The term of `liftFunctorToComplex` in bidegree `(n, q)`. -/
lemma liftFunctorToComplex_X_X (n : ℕ) (q : ℤ) :
    ((liftFunctorToComplex P hP F).X n).X q = (P.obj (F.X q)).X n :=
  rfl

/-- The double complex vanishes in the inner degrees below a bound of the complex. -/
lemma isZero_liftFunctorToComplexExtend_X_X (a : ℤ) [F.IsStrictlyGE a] (p q : ℤ) (hq : q < a) :
    IsZero (((liftFunctorToComplexExtend P hP F).X p).X q) := by
  by_cases hp : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = p
  · obtain ⟨n, rfl⟩ := hp
    have := hP n
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval D (ComplexShape.up ℤ) q).mapIso
      ((liftFunctorToComplex P hP F).extendXIso ComplexShape.embeddingUpNat
        (i := n) (i' := ComplexShape.embeddingUpNat.f n) rfl))
    exact Functor.map_isZero (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n)
      (F.isZero_of_isStrictlyGE a q hq)
  · exact (HomologicalComplex.eval D (ComplexShape.up ℤ) q).map_isZero
      ((liftFunctorToComplex P hP F).isZero_extend_X ComplexShape.embeddingUpNat p
        fun n hn => hp ⟨n, hn⟩)

/-- The double complex vanishes in the negative outer degrees, those outside the image of the
embedding of `ℕ` in `ℤ`. -/
lemma isZero_liftFunctorToComplexExtend_X_X_of_neg (p q : ℤ) (hp : p < 0) :
    IsZero (((liftFunctorToComplexExtend P hP F).X p).X q) :=
  (HomologicalComplex.eval D (ComplexShape.up ℤ) q).map_isZero
    ((liftFunctorToComplex P hP F).isZero_extend_X ComplexShape.embeddingUpNat p
      fun n (hn : (n : ℤ) = p) => by omega)

end Extend

end Preadditive2

section ExtendAbelian

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Abelian D]
  (P : C ⥤ CochainComplex D ℕ)
  (hP : ∀ n, (P ⋙ HomologicalComplex.eval D (ComplexShape.up ℕ) n).PreservesZeroMorphisms)
  (F : CochainComplex C ℤ)

/-- **The double complex has finite diagonals**: in total degree `n` its nonzero terms have outer
degree between `0` and `n - a`, where `a` is a bound of the complex. -/
lemma diagonalFinite_liftFunctorToComplexExtend (a : ℤ) [F.IsStrictlyGE a] :
    _root_.DiagonalFinite
      (liftFunctorToComplexExtend P hP F) := by
  intro k
  refine (Set.finite_Icc 0 (k - a)).subset fun p hnonzero => ⟨?_, ?_⟩
  · by_contra h
    exact hnonzero (isZero_liftFunctorToComplexExtend_X_X_of_neg P hP F p (k - p) (by omega))
  · by_contra h
    exact hnonzero (isZero_liftFunctorToComplexExtend_X_X P hP F a p (k - p) (by omega))

/-- The double complex has a total complex, its diagonals being finite. -/
lemma hasTotal_liftFunctorToComplexExtend (a : ℤ) [F.IsStrictlyGE a] :
    (liftFunctorToComplexExtend P hP F).HasTotal (ComplexShape.up ℤ) :=
  _root_.hasTotal_of_diagonalFinite _
    (diagonalFinite_liftFunctorToComplexExtend P hP F a)

/-- **The total complex is bounded below by the bound of the complex**: a summand of the total
complex in degree `n < a` has either a negative outer degree or an inner degree below `a`. -/
lemma isStrictlyGE_total_liftFunctorToComplexExtend (a : ℤ) [F.IsStrictlyGE a]
    [(liftFunctorToComplexExtend P hP F).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsStrictlyGE
      ((liftFunctorToComplexExtend P hP F).total (ComplexShape.up ℤ)) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let Z := liftFunctorToComplexExtend P hP F
  have hq : ∀ p q, q < 0 → IsZero ((Z.flip.X p).X q) := fun p q hq =>
    isZero_liftFunctorToComplexExtend_X_X_of_neg P hP F q p hq
  have hp : ∀ p, p < a → IsZero (Z.flip.X p) := by
    intro p hp
    rw [IsZero.iff_id_eq_zero]
    ext q
    exact (isZero_liftFunctorToComplexExtend_X_X P hP F a q p hp).eq_of_src _ _
  have : Z.flip.HasTotal (ComplexShape.up ℤ) :=
    (Z.flip_hasTotal_iff (ComplexShape.up ℤ)).2 inferInstance
  exact (StacksDraft.TotalComplexQuasiIso.isZero_total_X Z.flip a hq hp n hn).of_iso
    ((HomologicalComplex.eval D (ComplexShape.up ℤ) n).mapIso
      (Z.totalFlipIso (ComplexShape.up ℤ)).symm)

/-- **The columns of the double complex are the extended complexes `P(F^p)`**: the `p`-th column
of the flip is the extension of the complex `P(F^p)` of shape `ℕ`. -/
noncomputable def liftFunctorToComplexExtendFlipXIso (p : ℤ) :
    (liftFunctorToComplexExtend P hP F).flip.X p ≅
      (P.obj (F.X p)).extend ComplexShape.embeddingUpNat :=
  mapExtendIso (HomologicalComplex.eval D (ComplexShape.up ℤ) p) ComplexShape.embeddingUpNat
    (liftFunctorToComplex P hP F)

/-- The component in degree `0` of the inverse of `liftFunctorToComplexExtendFlipXIso`. -/
lemma liftFunctorToComplexExtendFlipXIso_inv_f_zero (p : ℤ) :
    (liftFunctorToComplexExtendFlipXIso P hP F p).inv.f 0 =
      ((P.obj (F.X p)).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        ((liftFunctorToComplex P hP F).extendXIso ComplexShape.embeddingUpNat rfl).inv.f p :=
  mapExtendIso_inv_f _ _ _ 0 0 rfl

end ExtendAbelian

/-! ### A quasi-isomorphism out of a complex concentrated in degree zero -/

/-- **A quasi-isomorphism from a complex concentrated in degree `0` exhibits its target as a
resolution.** If `M[0] ⟶ K` is a quasi-isomorphism and `K` vanishes in degree `-1`, then `K` is
exact away from degree `0` and the map `M ⟶ K^0` identifies `M` with the kernel of `K^0 ⟶ K^1`.

These are exactly the hypotheses on the columns of a double complex in [Stacks, Tag 0133]. -/
lemma exactAt_and_isIso_kernelLift_of_quasiIso_single
    {A : Type*} [Category A] [Abelian A]
    (M : A) (K : CochainComplex A ℤ)
    (f : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M ⟶ K)
    (hf : QuasiIso f) (hKneg : IsZero (K.X (-1))) :
    (∀ q : ℤ, q ≠ 0 → K.ExactAt q) ∧
      ∃ hα : f.f 0 ≫ K.d 0 1 = 0,
        IsIso (kernel.lift (K.d 0 1) (f.f 0) hα) := by
  refine ⟨fun q hq => (exactAt_iff_of_quasiIsoAt f q).1 (HomologicalComplex.ExactAt.of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M q hq)), ?_⟩
  have hα : f.f 0 ≫ K.d 0 1 = 0 := by
    rw [f.comm, HomologicalComplex.single_obj_d, zero_comp]
  refine ⟨hα, ?_⟩
  let S := (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M
  have : IsIso (S.homologyπ 0) := S.isIso_homologyπ (-1) 0 (by simp) (by simp [S])
  have : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0 (by simp) (hKneg.eq_of_src _ _)
  have : IsIso (HomologicalComplex.cyclesMap f 0 ≫ K.homologyπ 0) := by
    rw [← HomologicalComplex.homologyπ_naturality]
    exact inferInstanceAs (IsIso (S.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0))
  have : IsIso (HomologicalComplex.cyclesMap f 0) := IsIso.of_isIso_comp_right _ (K.homologyπ 0)
  have : IsIso (S.iCycles 0) := S.isIso_iCycles 0 1 (by simp) (by simp [S])
  let hK := K.cyclesIsKernel 0 1 (by simp)
  let e : K.cycles 0 ≅ kernel (K.d 0 1) := IsLimit.conePointUniqueUpToIso hK (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (K.d 0 1) = K.iCycles 0 :=
    IsLimit.conePointUniqueUpToIso_hom_comp hK (limit.isLimit _) WalkingParallelPair.zero
  have heq : HomologicalComplex.cyclesMap f 0 ≫ e.hom =
      S.iCycles 0 ≫ kernel.lift (K.d 0 1) (f.f 0) hα := by
    apply (cancel_mono (kernel.ι (K.d 0 1))).mp
    simp only [Category.assoc, he, HomologicalComplex.cyclesMap_i, kernel.lift_ι, S]
  have : IsIso (S.iCycles 0 ≫ kernel.lift (K.d 0 1) (f.f 0) hα) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (S.iCycles 0) _

end HomologicalComplex


end
