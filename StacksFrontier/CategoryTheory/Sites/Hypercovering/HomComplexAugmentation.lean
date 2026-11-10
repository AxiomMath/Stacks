module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroCanonical
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Injectives

/-!
# The augmentation of the Hom complex of an augmented simplicial presheaf

Let `C` be a category with a Grothendieck topology `J` and let `A` be an augmented simplicial
presheaf of sets on `C`.  Applying `Hom(-, F)` to the complex `s(**Z**_A^♯)` of free abelian
sheaves of `A` gives a cochain complex of abelian groups, *functorially in the coefficient sheaf*
`F`; and the degree-zero augmentation
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafAugZero` of that complex induces, by
precomposition, a map from the sections of `F` over the presheaf of augmentation points into it.

This file assembles that map into a natural transformation

  `ε : Γ_A(-)[0] ⟶ T_A(-)`

of functors `Sheaf J AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℤ`, and proves that `ε F` is a
quasi-isomorphism whenever `F` is injective and `A` is locally covering.  Those are exactly the
data `(T, ε, hε, hT0, hεinj)` consumed by
`StacksDraft.DerivedSectionsComparison.exists_comparison_of_hasFunctorialInjectiveEmbeddings`,
the abstract form of [Stacks, Tag 09VX]: the comparison map there is built out of an additive
functor `T` vanishing in negative degrees together with an augmentation which is a
quasi-isomorphism at injective objects.

The two inputs are already in the library and are used rather than reproved.  In degree zero,
`isIso_kernelLift_freeAbelianSheafAugZero` says that restriction along the augmentation is a
kernel of the first differential — this is [Stacks, Tag 09VV] in canonical-map form.  In positive
degrees, `isZero_sheafHomology_of_isLocallySurjective_matchingMaps` ([Stacks, Tag 01GE]) says that
`s(**Z**_A^♯)` is acyclic, and since `F` is injective the functor `Hom(-, F)` is exact, so the Hom
complex is exact there too; that is the argument of [Stacks, Tag 09VW].

## Main definitions

* `ChainComplex.homComplexFunctor`: for a chain complex `K` in a preadditive category, the functor
  `F ↦ Hom(K_•, F)` into cochain complexes of abelian groups.
* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafSections`: the functor
  `F ↦ Hom(**Z**_{A_right}^♯, F)`, the sections of `F` over the presheaf of augmentation points.
* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafHomCx` and
  `freeAbelianSheafHomCxZ`: the Hom complex functor of `s(**Z**_A^♯)`, indexed by `ℕ` and
  by `ℤ`.
* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNat` and
  `freeAbelianSheafEps`: the augmentation, indexed by `ℕ` and by `ℤ`.

## Main results

* `CochainComplex.quasiIso_mkHomFromSingle_zero`: a map out of a complex concentrated in degree
  zero is a quasi-isomorphism as soon as its degree-zero component is a kernel of the first
  differential and the target is exact everywhere else.  This is the converse of
  `StacksDraft.DerivedSectionsComparison.isIso_kernelLift_augZero`, read at `ℕ`.
* `ChainComplex.exactAt_homComplexFunctor_obj`: the Hom complex into an injective object is exact
  wherever the chain complex has vanishing homology.
* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEps_naturality` and
  `isZero_freeAbelianSheafHomCxZ_obj_X`: the naturality of `ε` in the coefficient sheaf, and the
  vanishing of `T_A` in negative degrees.
* `CategoryTheory.SimplicialObject.Augmented.quasiIso_freeAbelianSheafEps`:
  `ε F` is a quasi-isomorphism for every injective `F`.
* `CategoryTheory.SimplicialObject.Augmented.exists_comparison_freeAbelianSheafHomCx`:
  [Stacks, Tag 09VX] for this augmented functor, obtained by feeding the data above to
  `StacksDraft.DerivedSectionsComparison.exists_comparison_of_hasFunctorialInjectiveEmbeddings`.
* `Stacks.CategoryTheory.Hypercovering.quasiIso_freeAbelianSheafEps_toAugmentedULift`: the
  quasi-isomorphy for the augmented simplicial presheaf of a hypercovering of a presheaf
  (Tag 09VU), for which the three local surjectivity hypotheses are conditions (1), (2) and (3)
  of a hypercovering and so need not be assumed.

## Implementation notes

No `@[stacks]` attribute is placed here, for the reason recorded in
`CohomologyZeroCanonical.lean` and in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ObjectSections/DerivedSectionsComparison.lean`:
the statements are about
the complex `s(**Z**_A^♯)` of an augmented simplicial presheaf and about an abstract additive
functor, not about Tag 01GX's Čech complex, and in the general statements the three defining
conditions of a hypercovering play no role.  The hypercovering specialisation at the end is the
instantiation of those statements, not the statement of Tag 09VX itself.

Three choices are forced rather than chosen.

First, the coefficient variance.  `T_A(F)` is written with `preadditiveYoneda.obj F`, i.e. as
`Hom(-, F)` applied to the complex, because that is the spelling in which
`isIso_kernelLift_freeAbelianSheafAugZero` states the degree-zero input, and the Hom complex's
`d 0 1` is then *literally* `(preadditiveYoneda.obj F).map (s(**Z**_A^♯).d 1 0).op`, so no bridge
is needed.  Functoriality in `F` is supplied by `preadditiveYoneda.map`, whose component at
`op X` is `(preadditiveCoyoneda.obj (op X)).map` by `rfl`; the latter spelling is used exactly
twice, to get `Functor.map_add` and `Functor.Additive`, and nowhere else, since mixing the two
spellings inside one composite is what makes `Category.assoc` stop firing.

Second, the indexing.  `s(**Z**_A^♯)` is a chain complex indexed by `ℕ`, so the Hom complex is a
cochain complex indexed by `ℕ`, while Tag 09VX's construction needs `CochainComplex _ ℤ`.  The
bridge is Mathlib's extension along `ComplexShape.embeddingUpNat`, and `ε` is assembled as
`(extendSingleIso _).inv ≫ extendMap εNat`, exactly as Mathlib's
`CategoryTheory.InjectiveResolution.ι'` is; the quasi-isomorphy then transfers through
`HomologicalComplex.quasiIso_extendMap_iff` with nothing to prove, and the naturality through
`extendSingleIso_inv_naturality`.  Proving the degree-zero kernel statement again for the
`ℤ`-indexed complex, which is the alternative, would mean transporting a `kernel.lift` across two
`extendXIso`s.

Third, `ChainComplex.homComplexFunctor` is stated for an arbitrary preadditive category rather
than for presheaves of abelian groups.  Byte-identical copies of its presheaf-valued
special case already exist in the development — `Stacks.IntegralCech.homComplexFunctor` and
`Stacks.CechSite.homComplexFunctor`, both for the integral Čech complex of Stacks 03AS — and
neither of them applies to a category of sheaves.  This one subsumes them and they should be
collapsed onto it.

## References

* [Stacks, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks, Tag 09VW](https://stacks.math.columbia.edu/tag/09VW)
* [Stacks, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V]
  {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The identification of the extension of a complex concentrated in degree `i` with the complex
concentrated in degree `e.f i` is natural in the object. -/
lemma extendSingleIso_inv_naturality (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i')
    {X Y : V} (g : X ⟶ Y) :
    (single V c' i').map g ≫ (extendSingleIso e Y i i' h).inv =
      (extendSingleIso e X i i' h).inv ≫ extendMap ((single V c i).map g) e := by
  ext
  rw [comp_f, comp_f, extendSingleIso_inv_f, extendSingleIso_inv_f, single_map_f_self,
    extendMap_f _ e h, single_map_f_self]
  simp

end HomologicalComplex

namespace ComplexShape.Embedding

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V]
  {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- **Extending a complex concentrated in degree `i` gives the complex concentrated in degree
`e.f i`**, naturally in the object: the natural-transformation form of
`HomologicalComplex.extendSingleIso`. -/
noncomputable def singleCompExtendFunctorIso (e : c.Embedding c') {i : ι} {i' : ι'}
    (h : e.f i = i') :
    HomologicalComplex.single V c i ⋙ e.extendFunctor V ≅ HomologicalComplex.single V c' i' :=
  NatIso.ofComponents (fun X => HomologicalComplex.extendSingleIso e X i i' h)
    (fun {X Y} g => by
      have hnat := HomologicalComplex.extendSingleIso_inv_naturality e h g
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq] at hnat
      exact hnat.symm)

/-- `singleCompExtendFunctorIso` for the embedding of `ℕ`-indexed into `ℤ`-indexed cochain
complexes. -/
noncomputable def singleUpNatCompExtendFunctorIso (V : Type u) [Category.{v} V] [Preadditive V]
    [HasZeroObject V] :
    HomologicalComplex.single V (ComplexShape.up ℕ) 0 ⋙ embeddingUpNat.extendFunctor V ≅
      HomologicalComplex.single V (ComplexShape.up ℤ) 0 :=
  embeddingUpNat.singleCompExtendFunctorIso (by simp)

end ComplexShape.Embedding

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Abelian V]

/-- **A map out of a complex concentrated in degree zero is a quasi-isomorphism in degree zero**
as soon as its degree-zero component is a kernel of the first differential.  For a cochain complex
indexed by `ℕ` there is nothing in degree `-1`, so no vanishing hypothesis is needed. -/
lemma quasiIsoAt_zero_mkHomFromSingle (K : CochainComplex V ℕ) {Z : V} (φ : Z ⟶ K.X 0)
    (hφ : ∀ k : ℕ, (ComplexShape.up ℕ).Rel 0 k → φ ≫ K.d 0 k = 0)
    (hker : IsIso (kernel.lift (K.d 0 1) φ (hφ 1 rfl))) :
    QuasiIsoAt (HomologicalComplex.mkHomFromSingle φ hφ) 0 := by
  have h1 : IsIso (((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).iCycles 0) :=
    ((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).isIso_iCycles 0 1 (by simp)
      (HomologicalComplex.single_obj_d _ _ _ _ _)
  have h2 : IsIso (((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).homologyπ 0) :=
    inferInstance
  have h3 : IsIso (K.homologyπ 0) := inferInstance
  let hK := K.cyclesIsKernel 0 1 (by simp)
  let e : K.cycles 0 ≅ kernel (K.d 0 1) :=
    IsLimit.conePointUniqueUpToIso hK (limit.isLimit _)
  have heq : HomologicalComplex.cyclesMap (HomologicalComplex.mkHomFromSingle φ hφ) 0 ≫ e.hom =
      ((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Z).hom ≫
          kernel.lift (K.d 0 1) φ (hφ 1 rfl) := by
    apply (cancel_mono (kernel.ι (K.d 0 1))).mp
    have he : e.hom ≫ kernel.ι (K.d 0 1) = K.iCycles 0 :=
      IsLimit.conePointUniqueUpToIso_hom_comp hK (limit.isLimit _) WalkingParallelPair.zero
    simp only [Category.assoc, he, kernel.lift_ι, HomologicalComplex.cyclesMap_i]
    rw [HomologicalComplex.mkHomFromSingle_f]
  have h5 : IsIso (HomologicalComplex.cyclesMap
      (HomologicalComplex.mkHomFromSingle φ hφ) 0 ≫ e.hom) := by
    rw [heq]
    infer_instance
  have h6 : IsIso (HomologicalComplex.cyclesMap (HomologicalComplex.mkHomFromSingle φ hφ) 0) :=
    IsIso.of_isIso_comp_right _ e.hom
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h7 : IsIso (((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).homologyπ 0 ≫
      HomologicalComplex.homologyMap (HomologicalComplex.mkHomFromSingle φ hφ) 0) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (((HomologicalComplex.single V (ComplexShape.up ℕ) 0).obj Z).homologyπ 0) _

/-- **A resolution criterion.**  A map from a complex concentrated in degree zero to a cochain
complex indexed by `ℕ` is a quasi-isomorphism as soon as its degree-zero component is a kernel of
the first differential and the target is exact in every nonzero degree. -/
lemma quasiIso_mkHomFromSingle_zero (K : CochainComplex V ℕ) {Z : V} (φ : Z ⟶ K.X 0)
    (hφ : ∀ k : ℕ, (ComplexShape.up ℕ).Rel 0 k → φ ≫ K.d 0 k = 0)
    (hker : IsIso (kernel.lift (K.d 0 1) φ (hφ 1 rfl)))
    (hex : ∀ q : ℕ, q ≠ 0 → K.ExactAt q) :
    QuasiIso (HomologicalComplex.mkHomFromSingle φ hφ) := by
  rw [quasiIso_iff]
  intro q
  by_cases hq : q = 0
  · subst hq
    exact quasiIsoAt_zero_mkHomFromSingle K φ hφ hker
  · exact (quasiIsoAt_iff_exactAt _ q (HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 Z q hq))).2 (hex q hq)

/-- Naturality of `mkHomFromSingle` can be checked in degree zero. -/
private lemma single_map_comp_mkHomFromSingle {K K' : CochainComplex V ℕ} {X X' : V}
    (a : X ⟶ X') (φ : X ⟶ K.X 0) (hφ : ∀ k : ℕ, (ComplexShape.up ℕ).Rel 0 k → φ ≫ K.d 0 k = 0)
    (φ' : X' ⟶ K'.X 0) (hφ' : ∀ k : ℕ, (ComplexShape.up ℕ).Rel 0 k → φ' ≫ K'.d 0 k = 0)
    (b : K ⟶ K') (h : a ≫ φ' = φ ≫ b.f 0) :
    (HomologicalComplex.single V (ComplexShape.up ℕ) 0).map a ≫
        HomologicalComplex.mkHomFromSingle φ' hφ' =
      HomologicalComplex.mkHomFromSingle φ hφ ≫ b := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [comp_f, comp_f, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomFromSingle_f,
    single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [cancel_epi]
  exact h

end CochainComplex

namespace ChainComplex

section

variable {W : Type u} [Category.{v} W] [Preadditive W]

/-- **The Hom complex of a chain complex, functorially in the target.**  For a chain complex `K`
indexed by `ℕ` in a preadditive category, this is the functor `F ↦ Hom(K_•, F)` into cochain
complexes of abelian groups: in degree `n` it is `Hom(K_n, F)`, and its differential is
precomposition with the differential of `K`. -/
noncomputable def homComplexFunctor (K : ChainComplex W ℕ) :
    W ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj F := ((preadditiveYoneda.obj F).mapHomologicalComplex _).obj K.op
  map {_ _} f := (NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) _).app K.op
  map_id F := by
    simp only [preadditiveYoneda.map_id]
    rfl
  map_comp f g := by
    simp only [preadditiveYoneda.map_comp]
    rfl

/-- The degree-`n` term of `Hom(K_•, F)` is `Hom(K_n, F)`. -/
lemma homComplexFunctor_obj_X (K : ChainComplex W ℕ) (F : W) (n : ℕ) :
    ((homComplexFunctor K).obj F).X n = (preadditiveYoneda.obj F).obj (op (K.X n)) := rfl

/-- The differential of `Hom(K_•, F)` is precomposition with the differential of `K`. -/
lemma homComplexFunctor_obj_d (K : ChainComplex W ℕ) (F : W) (n m : ℕ) :
    ((homComplexFunctor K).obj F).d n m = (preadditiveYoneda.obj F).map (K.d m n).op := rfl

/-- In degree `n`, the map induced by `f : F ⟶ F'` is postcomposition with `f` on `Hom(K_n, -)`.
-/
lemma homComplexFunctor_map_f (K : ChainComplex W ℕ) {F F' : W} (f : F ⟶ F') (n : ℕ) :
    ((homComplexFunctor K).map f).f n = (preadditiveYoneda.map f).app (op (K.X n)) := rfl

/-- The Hom complex functor is additive. -/
instance (K : ChainComplex W ℕ) : (homComplexFunctor K).Additive where
  map_add {F F' f g} := by
    apply HomologicalComplex.hom_f_injective
    funext n
    change ((homComplexFunctor K).map (f + g)).f n =
      ((homComplexFunctor K).map f + (homComplexFunctor K).map g).f n
    rw [HomologicalComplex.add_f_apply, homComplexFunctor_map_f, homComplexFunctor_map_f,
      homComplexFunctor_map_f]
    change (preadditiveCoyoneda.obj (op (K.X n))).map (f + g) =
      (preadditiveCoyoneda.obj (op (K.X n))).map f + (preadditiveCoyoneda.obj (op (K.X n))).map g
    exact Functor.map_add _

end

section

variable {W : Type u} [Category.{v} W] [Abelian W]

/-- **The Hom complex into an injective object is exact wherever the chain complex is.**  For
`F` injective, `Hom(K_•, F)` is exact in every degree `n` in which `K` has vanishing homology. -/
lemma exactAt_homComplexFunctor_obj (K : ChainComplex W ℕ) (F : W) [Injective F]
    (n : ℕ) (h : IsZero (K.homology n)) : ((homComplexFunctor K).obj F).ExactAt n := by
  have hExactOp : K.op.ExactAt n :=
    (HomologicalComplex.exactAt_iff_isZero_homology K.op n).2
      (IsZero.of_iso h.op (K.homologyOp n))
  rw [HomologicalComplex.exactAt_iff] at hExactOp ⊢
  exact (hExactOp.map (preadditiveYonedaObj F)).map
    (forget₂ (ModuleCat (End F)) AddCommGrpCat.{v})

/-- **Exactness of the Hom complex in a positive degree is an extension property of the
opcycles.**  The Hom complex `Hom(K_•, F)` of an `ℕ`-indexed chain complex is exact in degree
`n + 1` exactly when every morphism out of `K.opcycles (n + 1)` into `F` extends along
`K.fromOpcycles (n + 1) n` to a morphism out of `K_n`. -/
lemma exactAt_homComplexFunctor_obj_succ_iff (K : ChainComplex W ℕ) (F : W) (n : ℕ) :
    ((homComplexFunctor K).obj F).ExactAt (n + 1) ↔
      ∀ a : K.opcycles (n + 1) ⟶ F, ∃ b : K.X n ⟶ F,
        K.fromOpcycles (n + 1) n ≫ b = a := by
  rw [((homComplexFunctor K).obj F).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  change (∀ x : K.X (n + 1) ⟶ F, K.d (n + 2) (n + 1) ≫ x = 0 →
      ∃ y : K.X n ⟶ F, K.d (n + 1) n ≫ y = x) ↔ _
  constructor
  · intro h a
    obtain ⟨b, hb⟩ := h (K.pOpcycles (n + 1) ≫ a)
      (by rw [← Category.assoc, K.d_pOpcycles, zero_comp])
    exact ⟨b, by rw [← cancel_epi (K.pOpcycles (n + 1)), ← Category.assoc,
      K.p_fromOpcycles, hb]⟩
  · intro h x hx
    obtain ⟨b, hb⟩ := h (K.descOpcycles x (n + 2) (by simp) hx)
    refine ⟨b, ?_⟩
    rw [← K.p_descOpcycles x (n + 2) (by simp) hx, ← hb, ← Category.assoc, K.p_fromOpcycles]

end

end ChainComplex

namespace CategoryTheory.SimplicialObject.Augmented

open AlgebraicTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))

/-- `Γ_A(F) = Hom(**Z**_{A_right}^♯, F)`: the sections of a sheaf of abelian groups over the
presheaf of augmentation points of `A`, functorially in the sheaf. -/
noncomputable def freeAbelianSheafSections :
    Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  preadditiveCoyoneda.obj (op ((Presheaf.freeAbelianSheaf J).obj A.right))

/-- `Γ_A` is additive. -/
instance : (freeAbelianSheafSections J A).Additive := by
  unfold freeAbelianSheafSections
  infer_instance

/-- `T_A(F) = Hom(s(**Z**_A^♯), F)`, indexed by `ℕ`: the complex of morphisms from the complex of
free abelian sheaves of `A` into a variable sheaf of abelian groups. -/
noncomputable def freeAbelianSheafHomCx :
    Sheaf J AddCommGrpCat.{w} ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  ChainComplex.homComplexFunctor ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left)

/-- The differential of `T_A(F)` is precomposition with the differential of `s(**Z**_A^♯)`. -/
lemma freeAbelianSheafHomCx_obj_d (F : Sheaf J AddCommGrpCat.{w}) (n m : ℕ) :
    ((freeAbelianSheafHomCx J A).obj F).d n m =
      (preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d m n).op := rfl

/-- In degree `n`, the map `T_A(f)` is postcomposition with `f` on `Hom(s(**Z**_A^♯)_n, -)`. -/
lemma freeAbelianSheafHomCx_map_f {F F' : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ F') (n : ℕ) :
    ((freeAbelianSheafHomCx J A).map f).f n = (preadditiveYoneda.map f).app
      (op (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).X n)) := rfl

/-- `T_A` is additive. -/
instance : (freeAbelianSheafHomCx J A).Additive := by
  unfold freeAbelianSheafHomCx
  infer_instance

/-- The degree-zero augmentation `Γ_A(F) ⟶ Hom(s(**Z**_A^♯)_0, F)`: restriction along
`freeAbelianSheafAugZero`.  The ascribed result type is what identifies the two `rfl`-equal
spellings `(preadditiveCoyoneda.obj (op Z)).obj F` and `(preadditiveYoneda.obj F).obj (op Z)` of
its source once and for all. -/
noncomputable def freeAbelianSheafEpsZero (F : Sheaf J AddCommGrpCat.{w}) :
    (freeAbelianSheafSections J A).obj F ⟶ ((freeAbelianSheafHomCx J A).obj F).X 0 :=
  (preadditiveYoneda.obj F).map (freeAbelianSheafAugZero J A).op

/-- The degree-zero augmentation is killed by the first differential of `T_A(F)`. -/
lemma freeAbelianSheafEpsZero_comp_d (F : Sheaf J AddCommGrpCat.{w}) (k : ℕ)
    (hk : (ComplexShape.up ℕ).Rel 0 k) :
    freeAbelianSheafEpsZero J A F ≫ ((freeAbelianSheafHomCx J A).obj F).d 0 k = 0 := by
  obtain rfl : k = 1 := by simpa using hk.symm
  change (preadditiveYoneda.obj F).map (freeAbelianSheafAugZero J A).op ≫
      (preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).d 1 0).op = 0
  rw [← Functor.map_comp, ← op_comp, d_comp_freeAbelianSheafAugZero, op_zero,
    Functor.map_zero]

/-- The augmentation `ε^ℕ_F : Γ_A(F)[0] ⟶ T_A(F)` of the `ℕ`-indexed Hom complex. -/
noncomputable def freeAbelianSheafEpsNat (F : Sheaf J AddCommGrpCat.{w}) :
    (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0).obj
        ((freeAbelianSheafSections J A).obj F) ⟶ (freeAbelianSheafHomCx J A).obj F :=
  HomologicalComplex.mkHomFromSingle (freeAbelianSheafEpsZero J A F)
    (freeAbelianSheafEpsZero_comp_d J A F)

/-- **The degree-zero augmentation is natural in the coefficient sheaf.** -/
lemma freeAbelianSheafEpsZero_naturality {F F' : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ F') :
    (freeAbelianSheafSections J A).map f ≫ freeAbelianSheafEpsZero J A F' =
      freeAbelianSheafEpsZero J A F ≫ ((freeAbelianSheafHomCx J A).map f).f 0 :=
  ((preadditiveYoneda.map f).naturality (freeAbelianSheafAugZero J A).op).symm

/-- **The augmentation is natural in the coefficient sheaf.** -/
lemma freeAbelianSheafEpsNat_naturality {F F' : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ F') :
    (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0).map
          ((freeAbelianSheafSections J A).map f) ≫ freeAbelianSheafEpsNat J A F' =
      freeAbelianSheafEpsNat J A F ≫ (freeAbelianSheafHomCx J A).map f :=
  CochainComplex.single_map_comp_mkHomFromSingle _ _ _ _ _ _
    (freeAbelianSheafEpsZero_naturality J A f)

/-- **The augmentation of the `ℕ`-indexed Hom complex is a quasi-isomorphism at an injective
sheaf**, when `A` is locally covering.  In degree zero this is [Stacks, Tag 09VV] in
canonical-map form, and in positive degrees it is [Stacks, Tag 09VW]: `s(**Z**_A^♯)` is acyclic by
[Stacks, Tag 01GE] and `Hom(-, F)` is exact. -/
theorem quasiIso_freeAbelianSheafEpsNat
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1)))))
    (F : Sheaf J AddCommGrpCat.{w}) [Injective F] :
    QuasiIso (freeAbelianSheafEpsNat J A F) :=
  CochainComplex.quasiIso_mkHomFromSingle_zero ((freeAbelianSheafHomCx J A).obj F)
    (freeAbelianSheafEpsZero J A F) (freeAbelianSheafEpsZero_comp_d J A F)
    (isIso_kernelLift_freeAbelianSheafAugZero J A h₀ h₁ F)
    (fun q hq => ChainComplex.exactAt_homComplexFunctor_obj _ F q
      (isZero_sheafHomology_of_isLocallySurjective_matchingMaps J A h₀ h₁ hm q
        (Nat.pos_of_ne_zero hq)))

/-- The augmentation of the `ℕ`-indexed Hom complex, as a natural transformation. -/
noncomputable def freeAbelianSheafEpsNatTransNat :
    freeAbelianSheafSections J A ⋙
        HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0 ⟶
      freeAbelianSheafHomCx J A where
  app F := freeAbelianSheafEpsNat J A F
  naturality _ _ f := freeAbelianSheafEpsNat_naturality J A f

/-! ### The `ℤ`-indexed form, as Tag 09VX's construction consumes it -/

/-- `T_A(F) = Hom(s(**Z**_A^♯), F)`, indexed by `ℤ`: the `ℕ`-indexed Hom complex extended by zero
in negative degrees. -/
noncomputable def freeAbelianSheafHomCxZ :
    Sheaf J AddCommGrpCat.{w} ⥤ CochainComplex AddCommGrpCat.{max u w} ℤ :=
  freeAbelianSheafHomCx J A ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}

/-- The `ℤ`-indexed `T_A` is additive. -/
instance : (freeAbelianSheafHomCxZ J A).Additive := by
  unfold freeAbelianSheafHomCxZ
  infer_instance

/-- The `ℤ`-indexed Hom complex is the extension by zero of the `ℕ`-indexed one. -/
lemma freeAbelianSheafHomCxZ_obj (F : Sheaf J AddCommGrpCat.{w}) :
    (freeAbelianSheafHomCxZ J A).obj F =
      ((freeAbelianSheafHomCx J A).obj F).extend ComplexShape.embeddingUpNat := rfl

/-- On morphisms, the `ℤ`-indexed Hom complex is the extension of the `ℕ`-indexed map. -/
lemma freeAbelianSheafHomCxZ_map (F F' : Sheaf J AddCommGrpCat.{w}) (f : F ⟶ F') :
    (freeAbelianSheafHomCxZ J A).map f =
      HomologicalComplex.extendMap ((freeAbelianSheafHomCx J A).map f)
        ComplexShape.embeddingUpNat := rfl

/-- **`T_A` vanishes in negative degrees.** -/
lemma isZero_freeAbelianSheafHomCxZ_obj_X (F : Sheaf J AddCommGrpCat.{w}) (q : ℤ) (hq : q < 0) :
    IsZero (((freeAbelianSheafHomCxZ J A).obj F).X q) := by
  rw [freeAbelianSheafHomCxZ_obj]
  exact HomologicalComplex.isZero_extend_X _ _ q (fun i => by
    simp only [ComplexShape.embeddingUpNat_f]
    omega)

/-- **The augmentation `ε : Γ_A(-)[0] ⟶ T_A(-)`**, indexed by `ℤ`, as a natural transformation.
It is assembled exactly as Mathlib's `CategoryTheory.InjectiveResolution.ι'` is: the
identification of the extension of a single complex with a single complex, followed by the
extension of the `ℕ`-indexed augmentation.  Keeping it a natural transformation rather than a
family of morphisms is what makes the naturality in the coefficient sheaf free; writing the
family out and composing by hand mixes the spellings `(freeAbelianSheafHomCxZ J A).obj F` and
`((freeAbelianSheafHomCx J A).obj F).extend ComplexShape.embeddingUpNat` of one object inside a
single composite, and then `Category.assoc` no longer applies to it. -/
noncomputable def freeAbelianSheafEpsNatTrans :
    freeAbelianSheafSections J A ⋙
        HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℤ) 0 ⟶
      freeAbelianSheafHomCxZ J A :=
  Functor.whiskerLeft (freeAbelianSheafSections J A)
      (ComplexShape.Embedding.singleUpNatCompExtendFunctorIso
        AddCommGrpCat.{max u w}).inv ≫
    Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J A)
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w})

/-- The augmentation `ε_F : Γ_A(F)[0] ⟶ T_A(F)` at a single coefficient sheaf. -/
noncomputable def freeAbelianSheafEps (F : Sheaf J AddCommGrpCat.{w}) :
    (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℤ) 0).obj
        ((freeAbelianSheafSections J A).obj F) ⟶ (freeAbelianSheafHomCxZ J A).obj F :=
  (freeAbelianSheafEpsNatTrans J A).app F

/-- The augmentation, unfolded: the single-complex identification followed by the extension of
the `ℕ`-indexed augmentation.  The ascribed statement is what identifies the spellings
`(freeAbelianSheafHomCxZ J A).obj F` and `((freeAbelianSheafHomCx J A).obj F).extend _`. -/
lemma freeAbelianSheafEps_eq (F : Sheaf J AddCommGrpCat.{w}) :
    freeAbelianSheafEps J A F =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            ((freeAbelianSheafSections J A).obj F) 0 0 (by simp)).inv ≫
        HomologicalComplex.extendMap (freeAbelianSheafEpsNat J A F)
          ComplexShape.embeddingUpNat := rfl

/-- **The augmentation is natural in the coefficient sheaf.** -/
lemma freeAbelianSheafEps_naturality {F F' : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ F') :
    (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℤ) 0).map
          ((freeAbelianSheafSections J A).map f) ≫ freeAbelianSheafEps J A F' =
      freeAbelianSheafEps J A F ≫ (freeAbelianSheafHomCxZ J A).map f :=
  (freeAbelianSheafEpsNatTrans J A).naturality f

/-- **The augmentation is a quasi-isomorphism at an injective sheaf**, when `A` is locally
covering. -/
theorem quasiIso_freeAbelianSheafEps
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1)))))
    (F : Sheaf J AddCommGrpCat.{w}) [Injective F] :
    QuasiIso (freeAbelianSheafEps J A F) := by
  have h : QuasiIso (freeAbelianSheafEpsNat J A F) :=
    quasiIso_freeAbelianSheafEpsNat J A h₀ h₁ hm F
  have key : QuasiIso ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        ((freeAbelianSheafSections J A).obj F) 0 0 (by simp)).inv ≫
      HomologicalComplex.extendMap (freeAbelianSheafEpsNat J A F)
        ComplexShape.embeddingUpNat) := inferInstance
  rw [freeAbelianSheafEps_eq]
  exact key

/-! ### The comparison map of Tag 09VX for this augmented functor -/

section

open StacksDraft.DerivedSectionsComparison

variable [HasDerivedCategory.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasDerivedCategory.{max u w} AddCommGrpCat.{max u w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- **[Stacks, Tag 09VX] for the Hom complex of a locally covering augmented simplicial
presheaf.**  There are a canonical map `ψ` from the sections of `F` over the presheaf of
augmentation points to the right derived functor of those sections at the single complex, and a
natural transformation `α : Hom(s(**Z**_A^♯), -) ⟶ R⁺Γ_A(-[0])` in `D⁺`, compatible with the
augmentation `ε`, and both are isomorphisms at every injective sheaf. -/
theorem exists_comparison_freeAbelianSheafHomCx
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1)))))
    (hFIE : HasFunctorialInjectiveEmbeddings (Sheaf J AddCommGrpCat.{w})) :
    ∃ (ψ : (freeAbelianSheafSections J A ⋙ singlePlus AddCommGrpCat.{max u w}) ⋙
          DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0 ⋙
          (freeAbelianSheafSections J A).rightDerivedFunctorPlus)
      (α : TPlus (freeAbelianSheafHomCxZ J A)
            (fun Y q hq => isZero_freeAbelianSheafHomCxZ_obj_X J A Y q hq) ⋙
          DerivedCategory.Plus.Q ⟶
        DerivedCategory.Plus.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0 ⋙
          (freeAbelianSheafSections J A).rightDerivedFunctorPlus),
      Functor.whiskerRight
            (epsNat (freeAbelianSheafSections J A) (freeAbelianSheafHomCxZ J A)
              (freeAbelianSheafEps J A)
              (fun {_ _} φ => freeAbelianSheafEps_naturality J A φ)
              (fun Y q hq => isZero_freeAbelianSheafHomCxZ_obj_X J A Y q hq))
            DerivedCategory.Plus.Q ≫ α = ψ ∧
        (∀ F : Sheaf J AddCommGrpCat.{w}, Injective F → IsIso (ψ.app F)) ∧
        (∀ F : Sheaf J AddCommGrpCat.{w}, Injective F → IsIso (α.app F)) :=
  exists_comparison_of_hasFunctorialInjectiveEmbeddings
    (Γ := freeAbelianSheafSections J A) (T := freeAbelianSheafHomCxZ J A)
    (ε := freeAbelianSheafEps J A)
    (hε := fun {_ _} φ => freeAbelianSheafEps_naturality J A φ)
    (hT0 := fun Y q hq => isZero_freeAbelianSheafHomCxZ_obj_X J A Y q hq)
    (hεinj := fun Y hY => by
      have := hY
      exact quasiIso_freeAbelianSheafEps J A h₀ h₁ hm Y)
    hFIE

end

end CategoryTheory.SimplicialObject.Augmented

/-! ### The Hom complex is contravariant in the chain complex -/

namespace ChainComplex

variable {W : Type u} [Category.{v} W] [Preadditive W]

/-- **The Hom complex out of a chain complex is contravariantly functorial in the complex.**  A
morphism `c : R ⟶ R'` of chain complexes gives, by precomposition, a morphism
`Hom(R'_•, -) ⟶ Hom(R_•, -)` of functors into cochain complexes. -/
noncomputable def homComplexFunctorPrecomp {R R' : ChainComplex W ℕ} (c : R ⟶ R') :
    homComplexFunctor R' ⟶ homComplexFunctor R where
  app F :=
    { f := fun n => (preadditiveYoneda.obj F).map (c.f n).op
      comm' := fun i j _ => by
        have key : (c.f i).op ≫ (R.d j i).op = (R'.d j i).op ≫ (c.f j).op := by
          rw [← op_comp, ← op_comp, c.comm j i]
        exact ((preadditiveYoneda.obj F).map_comp (c.f i).op (R.d j i).op).symm.trans
          ((congrArg ((preadditiveYoneda.obj F).map) key).trans
            ((preadditiveYoneda.obj F).map_comp (R'.d j i).op (c.f j).op)) }
  naturality {F F'} g :=
    HomologicalComplex.hom_ext _ _ fun n =>
      ((preadditiveYoneda.map g).naturality (c.f n).op).symm

/-- In degree `n`, precomposition along `c` is precomposition with `c.f n`. -/
@[simp]
lemma homComplexFunctorPrecomp_app_f {R R' : ChainComplex W ℕ} (c : R ⟶ R') (F : W) (n : ℕ) :
    ((homComplexFunctorPrecomp c).app F).f n = (preadditiveYoneda.obj F).map (c.f n).op :=
  rfl

end ChainComplex

/-! ### The augmentation of the Hom complex is contravariant in the augmented simplicial presheaf
-/

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- **The Hom complex of an augmented simplicial presheaf is contravariantly functorial in the
presheaf**: precomposition with the free abelian sheaves of the component of the morphism at the
simplicial part. -/
noncomputable def freeAbelianSheafHomCxPrecomp
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B) :
    freeAbelianSheafHomCx J B ⟶ freeAbelianSheafHomCx J A :=
  ChainComplex.homComplexFunctorPrecomp
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).map a.left)

/-- **The sections over the augmentation points are contravariantly functorial in the augmented
simplicial presheaf**, by precomposition with the free abelian sheaf of the component of the
morphism at the augmentation points. -/
noncomputable def freeAbelianSheafSectionsPrecomp {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)}
    (a : A ⟶ B) : freeAbelianSheafSections J B ⟶ freeAbelianSheafSections J A :=
  preadditiveCoyoneda.map ((Presheaf.freeAbelianSheaf J).map a.right).op

/-- At a sheaf `F`, the map on sections is precomposition with the free abelian sheaf of
`a.right`. -/
@[simp]
lemma freeAbelianSheafSectionsPrecomp_app
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B)
    (F : Sheaf J AddCommGrpCat.{w}) :
    (freeAbelianSheafSectionsPrecomp J a).app F =
      (preadditiveYoneda.obj F).map ((Presheaf.freeAbelianSheaf J).map a.right).op :=
  rfl

/-- The same map on the `ℤ`-indexed Hom complexes. -/
noncomputable def freeAbelianSheafHomCxZPrecomp
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B) :
    freeAbelianSheafHomCxZ J B ⟶ freeAbelianSheafHomCxZ J A :=
  Functor.whiskerRight (freeAbelianSheafHomCxPrecomp J a)
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w})

/-- **The degree-zero augmentation is natural in the augmented simplicial presheaf.** -/
theorem freeAbelianSheafEpsZero_comp_homCxPrecomp
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B)
    (F : Sheaf J AddCommGrpCat.{w}) :
    freeAbelianSheafEpsZero J B F ≫ ((freeAbelianSheafHomCxPrecomp J a).app F).f 0 =
      (preadditiveYoneda.obj F).map ((Presheaf.freeAbelianSheaf J).map a.right).op ≫
        freeAbelianSheafEpsZero J A F := by
  have hw : a.left.app (op (SimplexCategory.mk 0)) ≫ B.hom.app (op (SimplexCategory.mk 0)) =
      A.hom.app (op (SimplexCategory.mk 0)) ≫ a.right :=
    congrArg (fun t => NatTrans.app t (op (SimplexCategory.mk 0))) a.w
  have hzero : ((SimplicialObject.freeAbelianSheafComplexFunctor J).map a.left).f 0 ≫
      freeAbelianSheafAugZero J B =
        freeAbelianSheafAugZero J A ≫ (Presheaf.freeAbelianSheaf J).map a.right :=
    ((Presheaf.freeAbelianSheaf J).map_comp (a.left.app (op (SimplexCategory.mk 0)))
        (B.hom.app (op (SimplexCategory.mk 0)))).symm.trans
      ((congrArg (Presheaf.freeAbelianSheaf J).map hw).trans
        ((Presheaf.freeAbelianSheaf J).map_comp
          (A.hom.app (op (SimplexCategory.mk 0))) a.right))
  have hL : freeAbelianSheafEpsZero J B F ≫ ((freeAbelianSheafHomCxPrecomp J a).app F).f 0 =
      (preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J).map a.left).f 0 ≫
          freeAbelianSheafAugZero J B).op :=
    ((preadditiveYoneda.obj F).map_comp (freeAbelianSheafAugZero J B).op
      (((SimplicialObject.freeAbelianSheafComplexFunctor J).map a.left).f 0).op).symm
  have hR : (preadditiveYoneda.obj F).map ((Presheaf.freeAbelianSheaf J).map a.right).op ≫
        freeAbelianSheafEpsZero J A F =
      (preadditiveYoneda.obj F).map
        (freeAbelianSheafAugZero J A ≫ (Presheaf.freeAbelianSheaf J).map a.right).op :=
    ((preadditiveYoneda.obj F).map_comp ((Presheaf.freeAbelianSheaf J).map a.right).op
      (freeAbelianSheafAugZero J A).op).symm
  exact hL.trans ((congrArg
    (fun t ↦ (preadditiveYoneda.obj F).map (Quiver.Hom.op t)) hzero).trans hR.symm)

/-- **The augmentation of the `ℕ`-indexed Hom complex is natural in the augmented simplicial
presheaf**, for a morphism which is the identity at the augmentation points: the augmentation of
`B` followed by precomposition along the morphism is the augmentation of `A`. -/
theorem freeAbelianSheafEpsNatTransNat_comp_homCxPrecomp
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B) :
    freeAbelianSheafEpsNatTransNat J B ≫ freeAbelianSheafHomCxPrecomp J a =
      Functor.whiskerRight (freeAbelianSheafSectionsPrecomp J a)
          (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0) ≫
        freeAbelianSheafEpsNatTransNat J A := by
  refine NatTrans.ext (funext fun F ↦ ?_)
  change freeAbelianSheafEpsNat J B F ≫ (freeAbelianSheafHomCxPrecomp J a).app F =
    (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0).map
      ((freeAbelianSheafSectionsPrecomp J a).app F) ≫ freeAbelianSheafEpsNat J A F
  exact (CochainComplex.single_map_comp_mkHomFromSingle _ _ _ _ _ _
    (freeAbelianSheafEpsZero_comp_homCxPrecomp J a F).symm).symm

/-- **The augmentation of the `ℤ`-indexed Hom complex is natural in the augmented simplicial
presheaf**, for a morphism which is the identity at the augmentation points. -/
theorem freeAbelianSheafEpsNatTrans_comp_homCxZPrecomp
    {A B : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)} (a : A ⟶ B) :
    freeAbelianSheafEpsNatTrans J B ≫ freeAbelianSheafHomCxZPrecomp J a =
      Functor.whiskerRight (freeAbelianSheafSectionsPrecomp J a)
          (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℤ) 0) ≫
        freeAbelianSheafEpsNatTrans J A := by
  have h1 : Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J B)
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}) ≫
        freeAbelianSheafHomCxZPrecomp J a =
      Functor.whiskerRight (Functor.whiskerRight (freeAbelianSheafSectionsPrecomp J a)
            (HomologicalComplex.single AddCommGrpCat.{max u w} (ComplexShape.up ℕ) 0))
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}) ≫
        Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J A)
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}) :=
    (Functor.whiskerRight_comp (freeAbelianSheafEpsNatTransNat J B)
          (freeAbelianSheafHomCxPrecomp J a)
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w})).symm.trans
      ((congrArg (fun t ↦ Functor.whiskerRight t
            (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}))
          (freeAbelianSheafEpsNatTransNat_comp_homCxPrecomp J a)).trans
        (Functor.whiskerRight_comp _ _
          (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w})))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ Functor.whiskerLeft (freeAbelianSheafSections J B)
        (ComplexShape.Embedding.singleUpNatCompExtendFunctorIso
          AddCommGrpCat.{max u w}).inv ≫ t) h1).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t ↦ t ≫ Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J A)
            (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}))
          (Functor.whiskerLeft_comp_whiskerRight (freeAbelianSheafSectionsPrecomp J a)
            (ComplexShape.Embedding.singleUpNatCompExtendFunctorIso
              AddCommGrpCat.{max u w}).inv))))


end CategoryTheory.SimplicialObject.Augmented

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialObject.Augmented

universe q

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- **The augmentation of the Hom complex of a hypercovering of a presheaf is a
quasi-isomorphism at an injective sheaf.**  The three local surjectivity hypotheses of
`quasiIso_freeAbelianSheafEps` are conditions (1), (2) and (3) of a hypercovering (Tag 09VU), so
for `HypercoveringOf.toAugmentedULift` they need not be assumed. -/
theorem quasiIso_freeAbelianSheafEps_toAugmentedULift
    (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) [Injective F] :
    QuasiIso (freeAbelianSheafEps J.toGrothendieck
      (K.toAugmentedULift.{q, w, v, u} J G) F) :=
  quasiIso_freeAbelianSheafEps J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G)
    (isLocallySurjective_toAugmentedULift_hom_app_zero.{q, w, v, u} J G K)
    (isLocallySurjective_edgesToFiberProduct_toAugmentedULift.{q, w, v, u} J G K)
    (fun n hn => isLocallySurjective_coskAdj_unit_app_toAugmentedULift.{q, w, v, u} J G K n hn) F

end Stacks.CategoryTheory.Hypercovering

end
