module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.CoveringSetOnALocalizedSite

/-!
# The free abelian Čech complex of a sheaf covering the final sheaf

Let `C` be a site and let `K` be a sheaf of sets on it which surjects onto the final sheaf. The
Čech nerve of `K ⟶ *` has `(K^{i+1})` in degree `i`, so the complex `s(**Z**_•^♯)` of free
abelian sheaves attached to it — `CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor`,
Stacks 01GB — is a resolution of `**Z**^♯` by the free abelian sheaves on the self powers of `K`.
This file records the three facts about that resolution which the proof of Stacks 0GN3 uses:

* each term is the free abelian sheaf on a self power of `K` (`freeCechObjIso`);
* it is exact in positive degrees (`freeCechExactAt`), which is Stacks 01GC;
* in degree zero the augmentation identifies its opcycles with the free abelian sheaf on the
  final sheaf, compatibly with the degree-zero term (`freeCechOpcyclesZeroIso` and
  `pOpcycles_comp_freeCechOpcyclesZeroDesc`), which is Stacks 01GC in degree zero.

## Main definitions

* `Stacks.Cohomology.CoveringSet.freeCechObjIso`: the degree-`i` term of the complex is the free
  abelian sheaf on `K^{i+1}`.
* `Stacks.Cohomology.CoveringSet.freeCechOpcyclesZeroIso`: the degree-zero opcycles of the complex
  are the free abelian sheaf on the final sheaf.
* `Stacks.Cohomology.CoveringSet.widePullbackTerminalIsoFiniteProduct` and
  `Stacks.Cohomology.CoveringSet.finiteProductIsoSheafPower`: the wide pullback of `n` copies of
  `K` over the final sheaf is their product, and that product is
  `Stacks.Cohomology.CoveringSet.sheafPower`.

## Main results

* `Stacks.Cohomology.CoveringSet.freeCechExactAt`: the complex is exact in positive degrees.
* `Stacks.Cohomology.CoveringSet.isIso_freeCechOpcyclesZeroDesc`: the degree-zero augmentation
  descends to an isomorphism out of the degree-zero opcycles.
* `Stacks.Cohomology.CoveringSet.pOpcycles_comp_freeCechOpcyclesZeroDesc`: that descent, read on
  the degree-zero term of the complex, is the degree-zero augmentation.

## Implementation notes

The degree-zero statement is taken from
`CategoryTheory.Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective`, which is
the `opcycles` presentation of Stacks 01GC in degree zero. Taking it in that presentation is what
makes `pOpcycles_comp_freeCechOpcyclesZeroDesc` hold by `HomologicalComplex.p_descOpcycles`,
i.e. by the defining property of `descOpcycles`, with no transparency manipulation: the
alternative route through `HomologicalComplex.isoHomologyι₀` and `homologyMap` forces the
degree-zero augmentation to be compared across the complex concentrated in degree zero, and that
comparison is not reducible.

The self powers are indexed so that degree `i` carries `K^{i+1}`, matching
`CategoryTheory.Arrow.cechNerve`, whose degree-`i` term is a wide pullback over `Fin (i + 1)`.

Everything is at the small-site convention of Stacks 0GN3: the site and the coefficients live in
one universe `u`.

## References

* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped Simplicial

universe u

namespace Stacks.Cohomology.CoveringSet

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Wide pullbacks over the final sheaf -/

/-- The product of `n` copies of a sheaf of sets is its `n`-th self power
`Stacks.Cohomology.CoveringSet.sheafPower`, which is built by iterating binary products. -/
public def finiteProductIsoSheafPower (K : Sheaf J (Type u)) (n : ℕ) :
    (∏ᶜ fun _ : Fin n => K) ≅ sheafPower J K n := by
  induction n with
  | zero =>
      refine ⟨terminal.from _, Pi.lift (fun i : Fin 0 => Fin.elim0 i), ?_, ?_⟩
      · exact Pi.hom_ext _ _ fun i => Fin.elim0 i
      · exact terminal.hom_ext _ _
  | succ n ih =>
      let e : (∏ᶜ fun _ : Fin (n + 1) => K) ≅ K ⨯ (∏ᶜ fun _ : Fin n => K) :=
        { hom := prod.lift (Pi.π _ 0) (Pi.lift (fun i => Pi.π _ i.succ))
          inv := Pi.lift (fun i => Fin.cases prod.fst (fun j => prod.snd ≫ Pi.π _ j) i)
          hom_inv_id := Pi.hom_ext _ _ fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
          inv_hom_id := prod.hom_ext (by simp) (Pi.hom_ext _ _ fun i => by simp) }
      exact e ≪≫ prod.mapIso (Iso.refl K) ih

/-- The wide pullback of `n` copies of a sheaf of sets over the final sheaf is their product:
the compatibility condition imposed by a wide pullback over a terminal object is vacuous. -/
public def widePullbackTerminalIsoFiniteProduct (K : Sheaf J (Type u)) (n : ℕ) :
    widePullback (⊤_ (Sheaf J (Type u))) (fun _ : Fin n => K) (fun _ => terminal.from K) ≅
      (∏ᶜ fun _ : Fin n => K) := by
  let f : ∀ _ : Fin n, K ⟶ ⊤_ (Sheaf J (Type u)) := fun _ => terminal.from K
  refine
    { hom := Pi.lift (fun i => WidePullback.π f i)
      inv := WidePullback.lift (terminal.from _)
        (fun i => Pi.π (fun _ : Fin n => K) i) (fun i => terminal.hom_ext _ _)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply WidePullback.hom_ext
    · intro i
      simp only [f, Category.assoc, Pi.lift_comp_π, WidePullback.lift_π, Category.id_comp]
    · exact terminal.hom_ext _ _
  · exact Pi.hom_ext _ _ fun i => by
      simp only [f, Category.assoc, WidePullback.lift_π, Pi.lift_comp_π, Category.id_comp]

/-! ### The terms of the free abelian Čech complex -/

variable {K T : Sheaf J (Type u)}

/-- The degree-`i` term of the Čech nerve of `K ⟶ *` is the underlying presheaf of `K^{i+1}`:
it is a wide pullback of `i + 1` copies of `K` over the final sheaf, which is their product
because the final sheaf is terminal, and taking underlying presheaves preserves that limit. -/
public def cechNerveObjIsoSheafPower (K : Sheaf J (Type u)) (i : ℕ) :
    (Arrow.mk (terminal.from K).hom).cechNerve.obj (op ⦋i⦌) ≅ (sheafPower J K (i + 1)).obj := by
  let U := sheafToPresheaf J (Type u)
  let D := WidePullbackShape.wideCospan (⊤_ (Sheaf J (Type u)))
    (fun _ : Fin (i + 1) => K) (fun _ => terminal.from K)
  let DP := WidePullbackShape.wideCospan (⊤_ (Sheaf J (Type u))).obj
    (fun _ : Fin (i + 1) => K.obj) (fun _ => (terminal.from K).hom)
  let eD : D ⋙ U ≅ DP :=
    NatIso.ofComponents (fun j => by cases j with
      | none => exact Iso.refl _
      | some j => exact Iso.refl _) (by
      intro a b g
      cases a <;> cases b <;> cases g <;>
        simp only [Category.id_comp, Category.comp_id, Iso.refl_hom] <;> rfl)
  let eW : U.obj (widePullback (⊤_ (Sheaf J (Type u))) (fun _ : Fin (i + 1) => K)
      (fun _ => terminal.from K)) ≅
      widePullback (⊤_ (Sheaf J (Type u))).obj (fun _ : Fin (i + 1) => K.obj)
        (fun _ => (terminal.from K).hom) :=
    preservesLimitIso U D ≪≫ HasLimit.isoOfNatIso eD
  exact eW.symm ≪≫ U.mapIso (widePullbackTerminalIsoFiniteProduct J K (i + 1) ≪≫
    finiteProductIsoSheafPower J K (i + 1))

/-- The degree-`i` term of the complex `s(**Z**_•^♯)` of the Čech nerve of `K ⟶ *` is the free
abelian sheaf on the self power `K^{i+1}`. -/
public def freeCechObjIso (K : Sheaf J (Type u)) (i : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk (terminal.from K).hom).cechNerve).X i ≅
      (Presheaf.freeAbelianSheaf J).obj (sheafPower J K (i + 1)).obj :=
  (Presheaf.freeAbelianSheaf J).mapIso (cechNerveObjIsoSheafPower J K i)

/-! ### Exactness -/

/-- **Stacks 01GC.** The complex `s(**Z**_•^♯)` of the Čech nerve of a surjection of sheaves of
sets is exact in positive degrees. -/
public lemma freeCechExactAt (f : K ⟶ T) (hf : Sheaf.IsLocallySurjective f) (n : ℕ) (hn : 0 < n) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f.hom).cechNerve).ExactAt
      n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Presheaf.isZero_sheafHomology_cechNerve_of_isLocallySurjective J f.hom hf n hn

/-! ### Degree zero -/

section Zero

variable (f : K ⟶ T)

/-- The degree-zero augmentation of the free abelian Čech complex of `f`, written out: the free
abelian sheaf functor applied to the unique projection of the degree-zero Čech term followed by
`f` itself. -/
public def freeCechAugmentationZero :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f.hom).cechNerve).X 0 ⟶
      (Presheaf.freeAbelianSheaf J).obj T.obj :=
  (Presheaf.freeAbelianSheaf J).map (WidePullback.π (fun _ : Fin 1 => f.hom) 0) ≫
    (Presheaf.freeAbelianSheaf J).map f.hom

/-- `freeCechAugmentationZero` is the degree-zero component of
`CategoryTheory.Presheaf.cechNerveSheafAugmentation`, read as a morphism to the free abelian
sheaf on the target: that component is the free abelian sheaf functor applied to the base map of
the wide pullback, and the base map factors as the unique projection followed by `f`. -/
public lemma cechNerveSheafAugmentation_f_zero_eq :
    (Presheaf.cechNerveSheafAugmentation J f.hom).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          ((Presheaf.freeAbelianSheaf J).obj T.obj)).hom =
      freeCechAugmentationZero J f := by
  rw [Presheaf.cechNerveSheafAugmentation_f_zero_comp_singleObjXSelf_hom,
    ← WidePullback.π_arrow (fun _ : Fin 1 => f.hom) 0, Functor.map_comp]
  rfl

/-- The degree-zero augmentation annihilates the incoming differential, hence descends through the
degree-zero opcycles. -/
public lemma d_comp_freeCechAugmentationZero (j : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f.hom).cechNerve).d j 0 ≫
      freeCechAugmentationZero J f = 0 :=
  Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J f.hom
    (cechNerveSheafAugmentation_f_zero_eq J f) j

/-- The descent of the degree-zero augmentation through the degree-zero opcycles of the free
abelian Čech complex of `f`. -/
public def freeCechOpcyclesZeroDesc :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk f.hom).cechNerve).opcycles 0 ⟶
      (Presheaf.freeAbelianSheaf J).obj T.obj :=
  ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk f.hom).cechNerve).descOpcycles (freeCechAugmentationZero J f) 1 (by simp)
    (d_comp_freeCechAugmentationZero J f 1)

/-- The defining property of `freeCechOpcyclesZeroDesc`: restricted to the degree-zero term of the
complex it is the degree-zero augmentation. -/
public lemma pOpcycles_comp_freeCechOpcyclesZeroDesc :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f.hom).cechNerve).pOpcycles 0 ≫ freeCechOpcyclesZeroDesc J f =
      freeCechAugmentationZero J f :=
  HomologicalComplex.p_descOpcycles _ _ _ _ _

/-- **Stacks 01GC in degree zero.** For a surjection `f` of sheaves of sets the degree-zero
augmentation of the free abelian Čech complex of `f` descends to an *isomorphism* from the
degree-zero opcycles onto the free abelian sheaf on the target.

Tag 01GC gives that descent restricted along the isomorphism `homologyι` out of degree-zero
homology, and `homologyι` in degree zero is invertible for a chain complex. -/
public lemma isIso_freeCechOpcyclesZeroDesc (hf : Sheaf.IsLocallySurjective f) :
    IsIso (freeCechOpcyclesZeroDesc J f) :=
  @IsIso.of_isIso_comp_left _ _ _ _ _
    (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk f.hom).cechNerve).homologyι 0) (freeCechOpcyclesZeroDesc J f) inferInstance
    (Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective J f.hom hf
      (cechNerveSheafAugmentation_f_zero_eq J f) 1 (by simp)
      (d_comp_freeCechAugmentationZero J f 1))

/-- **Stacks 01GC in degree zero.** The degree-zero opcycles of the free abelian Čech complex of a
surjection `f` of sheaves of sets are the free abelian sheaf on the target of `f`, by the
degree-zero augmentation; see `pOpcycles_comp_freeCechOpcyclesZeroDesc` for the compatibility with
the degree-zero term of the complex. -/
public def freeCechOpcyclesZeroIso (hf : Sheaf.IsLocallySurjective f) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk f.hom).cechNerve).opcycles 0 ≅
      (Presheaf.freeAbelianSheaf J).obj T.obj :=
  @asIso _ _ _ _ (freeCechOpcyclesZeroDesc J f) (isIso_freeCechOpcyclesZeroDesc J f hf)

/-- `freeCechOpcyclesZeroIso`, read on the degree-zero term of the complex, is the free abelian
sheaf functor applied to the unique projection of the degree-zero Čech term followed by `f`. -/
public lemma pOpcycles_comp_freeCechOpcyclesZeroIso_hom (hf : Sheaf.IsLocallySurjective f) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f.hom).cechNerve).pOpcycles 0 ≫ (freeCechOpcyclesZeroIso J f hf).hom =
      (Presheaf.freeAbelianSheaf J).map (WidePullback.π (fun _ : Fin 1 => f.hom) 0) ≫
        (Presheaf.freeAbelianSheaf J).map f.hom :=
  pOpcycles_comp_freeCechOpcyclesZeroDesc J f

end Zero

end Stacks.Cohomology.CoveringSet

end
