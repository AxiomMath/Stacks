module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Localization

/-!
# Extension of complexes along an embedding of shapes, against functors and homology

Let `e : c.Embedding c'` be an embedding of complex shapes. Extension by zero along `e` is a
functor `HomologicalComplex A c ⥤ HomologicalComplex A c'`, and Mathlib knows that it does not
change homology in the degrees `e` hits (`HomologicalComplex.extendHomologyIso`) and that it
descends to homotopy categories (`ComplexShape.Embedding.extendHomotopyFunctor`). This file
shows that extension commutes with an additive functor applied termwise, naturally in the
functor, and that the homology comparison is natural, both on complexes and on homotopy
categories.

## Main definitions

* `Stacks.DerivedIndexing.mapExtendNatIso`: for an additive `F : A ⥤ B`, extension along `e`
  commutes with `F` applied termwise.
* `Stacks.DerivedIndexing.mapExtendXIsoSymm`: the degreewise comparison in the inverse direction,
  for a functor that merely preserves zero morphisms.
* `Stacks.DerivedIndexing.mapExtendHomotopyNatIso`: the same on homotopy categories.
* `Stacks.DerivedIndexing.extendHomologyNatIso`: `H^{e.f j}(K.extend e) ≅ H^j(K)`, naturally
  in `K`.
* `Stacks.DerivedIndexing.extendHomotopyHomologyNatIso`: the same on homotopy categories.

## Main results

* `Stacks.DerivedIndexing.mapExtendIso_hom_f_eq`,
  `Stacks.DerivedIndexing.mapExtendIso_hom_f_comp_map_extendXIso`,
  `Stacks.DerivedIndexing.extendXIso_inv_comp_mapExtendIso_hom_f`: the degreewise closed form of
  the termwise comparison in a degree in the range of the embedding.
* `Stacks.DerivedIndexing.mapExtendNatIso_hom_natTrans`,
  `Stacks.DerivedIndexing.mapExtendHomotopyNatIso_hom_natTrans`: the termwise comparison is
  natural in the additive functor — for `α : F ⟶ G`, applying `α` termwise before extending by
  zero agrees with applying it afterwards.
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex

namespace Stacks.DerivedIndexing

universe v v' u u'

section

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
  (F : A ⥤ B) [F.Additive]

/-- The comparison, in a single degree, between extending a complex by zero and then applying an
additive functor `F` termwise, and applying `F` termwise and then extending by zero. The degree
is presented as an `Option ι`, as in the definition of `HomologicalComplex.extend`. -/
noncomputable def mapExtendXIso (K : HomologicalComplex A c) :
    ∀ i : Option ι, extend.X ((F.mapHomologicalComplex c).obj K) i ≅ F.obj (extend.X K i)
  | some _ => Iso.refl _
  | none => F.mapZeroObject.symm

/-- `mapExtendXIso` is compatible with the differentials of the two extensions. -/
lemma mapExtendXIso_d (K : HomologicalComplex A c) (i j : Option ι) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.d K i j) =
      extend.d ((F.mapHomologicalComplex c).obj K) i j ≫ (mapExtendXIso F K j).hom := by
  cases i with
  | none => exact (extend.isZero_X _ rfl).eq_of_src _ _
  | some a =>
    cases j with
    | none => exact (F.map_isZero (extend.isZero_X K rfl)).eq_of_tgt _ _
    | some b => exact (id_comp _).trans (comp_id _).symm

/-- `mapExtendXIso` is compatible with the morphisms induced on the two extensions. -/
lemma mapExtendXIso_mapX {K L : HomologicalComplex A c} (φ : K ⟶ L) (i : Option ι) :
    extend.mapX ((F.mapHomologicalComplex c).map φ) i ≫ (mapExtendXIso F L i).hom =
      (mapExtendXIso F K i).hom ≫ F.map (extend.mapX φ i) := by
  cases i with
  | none => exact (extend.isZero_X _ rfl).eq_of_src _ _
  | some a => exact (comp_id _).trans (id_comp _).symm

/-- **The closed form of `mapExtendXIso` in a degree hit by the embedding.** There the two
extensions have the same term, and the comparison is the composite of the two identifications of
that term with `F` applied to the term of `K`. -/
lemma mapExtendXIso_eq (K : HomologicalComplex A c) {j : Option ι} {a : ι} (hj : j = some a) :
    mapExtendXIso F K j =
      extend.XIso ((F.mapHomologicalComplex c).obj K) hj ≪≫
        (F.mapIso (extend.XIso K hj)).symm := by
  subst hj
  refine Iso.ext ?_
  simp only [mapExtendXIso, Iso.refl_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    extend.XIso, eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans]
  exact (eqToHom_refl _ _).symm

/-- `mapExtendXIso_eq`, for the forward morphism. -/
lemma mapExtendXIso_hom_eq (K : HomologicalComplex A c) {j : Option ι} {a : ι}
    (hj : j = some a) :
    (mapExtendXIso F K j).hom =
      (extend.XIso ((F.mapHomologicalComplex c).obj K) hj).hom ≫
        F.map (extend.XIso K hj).inv :=
  congrArg Iso.hom (mapExtendXIso_eq F K hj)

/-- `mapExtendXIso_eq`, for the inverse. -/
lemma mapExtendXIso_inv_eq (K : HomologicalComplex A c) {j : Option ι} {a : ι}
    (hj : j = some a) :
    (mapExtendXIso F K j).inv =
      F.map (extend.XIso K hj).hom ≫
        (extend.XIso ((F.mapHomologicalComplex c).obj K) hj).inv :=
  congrArg Iso.inv (mapExtendXIso_eq F K hj)

variable (e : c.Embedding c')

/-- Applying an additive functor `F` termwise to the extension by zero of `K` along `e` gives
the extension by zero of `F` applied termwise to `K`. -/
noncomputable def mapExtendIso (K : HomologicalComplex A c) :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  Hom.isoOfComponents (fun i' ↦ mapExtendXIso F K (e.r i'))
    (fun _ _ _ ↦ mapExtendXIso_d F K _ _)

/-- **The degreewise closed form of `mapExtendIso` in a degree in the range of the
embedding.** -/
lemma mapExtendIso_hom_f_eq (K : HomologicalComplex A c) {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendIso F e K).hom.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv :=
  mapExtendXIso_hom_eq F K (e.r_eq_some h)

/-- `mapExtendIso_hom_f_eq`, for the inverse. -/
lemma mapExtendIso_inv_f_eq (K : HomologicalComplex A c) {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendIso F e K).inv.f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  mapExtendXIso_inv_eq F K (e.r_eq_some h)

/-- `mapExtendIso`, read through the comparison isomorphisms at a degree in the range of the
embedding. -/
lemma mapExtendIso_hom_f_comp_map_extendXIso (K : HomologicalComplex A c) {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (mapExtendIso F e K).hom.f i' ≫ F.map (K.extendXIso e h).hom =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom := by
  rw [mapExtendIso_hom_f_eq F e K h, Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id]
  exact Category.comp_id _

/-- `mapExtendIso`, read through the comparison isomorphism of the source at a degree in the
range of the embedding. -/
lemma extendXIso_inv_comp_mapExtendIso_hom_f (K : HomologicalComplex A c) {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv ≫ (mapExtendIso F e K).hom.f i' =
      F.map (K.extendXIso e h).inv := by
  rw [mapExtendIso_hom_f_eq F e K h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Extension by zero along `e` commutes with an additive functor applied termwise. -/
noncomputable def mapExtendNatIso :
    F.mapHomologicalComplex c ⋙ e.extendFunctor B ≅
      e.extendFunctor A ⋙ F.mapHomologicalComplex c' :=
  NatIso.ofComponents (fun K ↦ mapExtendIso F e K) (fun _ ↦ by
    ext i'
    exact mapExtendXIso_mapX F _ (e.r i'))

variable [e.IsRelIff]

/-- The comparison `mapExtendNatIso`, read after the quotient functor to the homotopy
category. -/
noncomputable def mapExtendHomotopyNatIsoAux :
    HomotopyCategory.quotient A c ⋙ (F.mapHomotopyCategory c ⋙ e.extendHomotopyFunctor B) ≅
      HomotopyCategory.quotient A c ⋙ (e.extendHomotopyFunctor A ⋙ F.mapHomotopyCategory c') :=
  Functor.isoWhiskerRight (mapExtendNatIso F e) (HomotopyCategory.quotient B c')

/-- Extension by zero along `e` commutes with an additive functor applied termwise, read on
homotopy categories. -/
noncomputable def mapExtendHomotopyNatIso :
    F.mapHomotopyCategory c ⋙ e.extendHomotopyFunctor B ≅
      e.extendHomotopyFunctor A ⋙ F.mapHomotopyCategory c' :=
  Quotient.natIsoLift _ (mapExtendHomotopyNatIsoAux F e)

/-- Extension by zero of a morphism of complexes, read on homotopy categories. -/
lemma extendHomotopyFunctor_map_quotient_map {K L : HomologicalComplex A c} (φ : K ⟶ L) :
    (e.extendHomotopyFunctor A).map ((HomotopyCategory.quotient A c).map φ) =
      (HomotopyCategory.quotient A c').map ((e.extendFunctor A).map φ) := rfl

/-- The components of `mapExtendHomotopyNatIso`: at a complex, it is the class of the
comparison `mapExtendIso` of complexes. -/
lemma mapExtendHomotopyNatIso_hom_app (K : HomologicalComplex A c) :
    (mapExtendHomotopyNatIso F e).hom.app ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.quotient B c').map (mapExtendIso F e K).hom := rfl

end

section PreservesZero

variable {ι : Type*} {c : ComplexShape ι}
  {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [HasZeroMorphisms A] [HasZeroObject A] [HasZeroMorphisms B] [HasZeroObject B]
  (G : A ⥤ B) [G.PreservesZeroMorphisms]

/-- The comparison, in a single degree, between applying `G` termwise to an extension by zero and
extending by zero the termwise image of `G`: in a degree hit by the embedding both sides are `G`
applied to a term of the complex, and in the remaining degrees both are zero objects. It goes in
the inverse direction to `mapExtendXIso`, for a functor `G` that preserves zero morphisms. -/
noncomputable def mapExtendXIsoSymm (K : HomologicalComplex A c) :
    ∀ o : Option ι, G.obj (extend.X K o) ≅ extend.X ((G.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => (G.map_isZero (extend.isZero_X K rfl)).iso (extend.isZero_X _ rfl)

/-- `mapExtendXIsoSymm` is compatible with the differentials of the two extensions. -/
lemma mapExtendXIsoSymm_d (K : HomologicalComplex A c) (a b : Option ι) :
    (mapExtendXIsoSymm G K a).hom ≫ extend.d ((G.mapHomologicalComplex c).obj K) a b =
      G.map (extend.d K a b) ≫ (mapExtendXIsoSymm G K b).hom := by
  cases a <;> cases b
  · exact (G.map_isZero (extend.isZero_X K rfl)).eq_of_src _ _
  · exact (G.map_isZero (extend.isZero_X K rfl)).eq_of_src _ _
  · exact (extend.isZero_X ((G.mapHomologicalComplex c).obj K) (i := none) rfl).eq_of_tgt _ _
  · exact (id_comp _).trans (comp_id _).symm

/-- `mapExtendXIsoSymm` is compatible with the morphisms induced on the two extensions. -/
lemma mapExtendXIsoSymm_mapX {K L : HomologicalComplex A c} (φ : K ⟶ L) (o : Option ι) :
    G.map (extend.mapX φ o) ≫ (mapExtendXIsoSymm G L o).hom =
      (mapExtendXIsoSymm G K o).hom ≫ extend.mapX ((G.mapHomologicalComplex c).map φ) o := by
  match o with
  | none => exact (G.map_isZero (extend.isZero_X K rfl)).eq_of_src _ _
  | some a =>
    exact (comp_id (G.map (extend.mapX φ (some a)))).trans
      (id_comp (extend.mapX ((G.mapHomologicalComplex c).map φ) (some a))).symm

/-- **The closed form of `mapExtendXIsoSymm` in a degree hit by the embedding.** There the two
extensions have the same term, and the comparison is the composite of the two identifications of
that term with `G` applied to the term of `K`. -/
lemma mapExtendXIsoSymm_hom_eq (K : HomologicalComplex A c) {o : Option ι} {a : ι}
    (ho : o = some a) :
    (mapExtendXIsoSymm G K o).hom =
      G.map (extend.XIso K ho).hom ≫ (extend.XIso ((G.mapHomologicalComplex c).obj K) ho).inv := by
  subst ho
  simp only [mapExtendXIsoSymm, Iso.refl_hom, extend.XIso, eqToIso.hom, eqToIso.inv, eqToHom_map,
    eqToHom_trans]
  exact (eqToHom_refl _ _).symm

section Embedding

variable {ι' : Type*} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- `mapExtendXIsoSymm_hom_eq` with the degree presented as an object `i'` of the target shape
rather than as an `Option ι`, and the two comparisons written with
`HomologicalComplex.extendXIso` rather than `HomologicalComplex.extend.XIso`. -/
lemma mapExtendXIsoSymm_hom_of_r_eq_some (K : HomologicalComplex A c) {i' : ι'} {i : ι}
    (h : e.r i' = some i) :
    (mapExtendXIsoSymm G K (e.r i')).hom =
      G.map (K.extendXIso e (ComplexShape.Embedding.f_eq_of_r_eq_some _ h)).hom ≫
        (((G.mapHomologicalComplex c).obj K).extendXIso e
          (ComplexShape.Embedding.f_eq_of_r_eq_some _ h)).inv :=
  mapExtendXIsoSymm_hom_eq G K h

/-- **Applying `G` degreewise commutes with extension by zero along an embedding of complex
shapes.** Extending `K` along `e` and then applying `G` degreewise gives the same complex as
applying `G` degreewise and then extending. -/
noncomputable def mapExtendIsoSymm (K : HomologicalComplex A c) :
    (G.mapHomologicalComplex c').obj (K.extend e) ≅
      ((G.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i' ↦ mapExtendXIsoSymm G K (e.r i'))
    (fun _ _ _ ↦ mapExtendXIsoSymm_d G K _ _)

/-- `mapExtendIsoSymm` is natural in the complex. -/
lemma mapExtendIsoSymm_naturality {K L : HomologicalComplex A c} (φ : K ⟶ L) :
    (G.mapHomologicalComplex c').map (extendMap φ e) ≫ (mapExtendIsoSymm G e L).hom =
      (mapExtendIsoSymm G e K).hom ≫ extendMap ((G.mapHomologicalComplex c).map φ) e := by
  ext i'
  exact mapExtendXIsoSymm_mapX G φ (e.r i')

/-- `mapExtendIsoSymm` read as an isomorphism of functors: extending along `e` and then applying
`G` degreewise agrees with applying `G` degreewise and then extending. -/
noncomputable def mapExtendNatIsoSymm :
    e.extendFunctor A ⋙ G.mapHomologicalComplex c' ≅
      G.mapHomologicalComplex c ⋙ e.extendFunctor B :=
  NatIso.ofComponents (fun K ↦ mapExtendIsoSymm G e K) (mapExtendIsoSymm_naturality G e)

end Embedding

end PreservesZero

section FunctorVariable

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
  {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)

/-- `mapExtendXIso` is natural in the additive functor: in a single degree, applying `α` termwise
commutes with the comparison between extending and applying the functor. -/
lemma mapExtendXIso_natTrans (K : HomologicalComplex A c) (i : Option ι) :
    extend.mapX ((NatTrans.mapHomologicalComplex α c).app K) i ≫ (mapExtendXIso G K i).hom =
      (mapExtendXIso F K i).hom ≫ α.app (extend.X K i) := by
  cases i with
  | none => exact (extend.isZero_X _ rfl).eq_of_src _ _
  | some a => exact (comp_id _).trans (id_comp _).symm

variable (e : c.Embedding c')

/-- `mapExtendIso` is natural in the additive functor. -/
lemma mapExtendIso_hom_natTrans (K : HomologicalComplex A c) :
    (e.extendFunctor B).map ((NatTrans.mapHomologicalComplex α c).app K) ≫
        (mapExtendIso G e K).hom =
      (mapExtendIso F e K).hom ≫ (NatTrans.mapHomologicalComplex α c').app (K.extend e) := by
  ext i'
  exact mapExtendXIso_natTrans α K (e.r i')

/-- **`mapExtendNatIso` is natural in the additive functor.** For `α : F ⟶ G` between additive
functors, applying `α` termwise before extending by zero along `e` agrees with applying it
afterwards, through the comparisons `mapExtendNatIso`. -/
lemma mapExtendNatIso_hom_natTrans :
    Functor.whiskerRight (NatTrans.mapHomologicalComplex α c) (e.extendFunctor B) ≫
        (mapExtendNatIso G e).hom =
      (mapExtendNatIso F e).hom ≫
        Functor.whiskerLeft (e.extendFunctor A) (NatTrans.mapHomologicalComplex α c') := by
  ext K : 2
  exact mapExtendIso_hom_natTrans α e K

variable [e.IsRelIff]

/-- **`mapExtendHomotopyNatIso` is natural in the additive functor**, the homotopy-category form
of `mapExtendNatIso_hom_natTrans`. -/
lemma mapExtendHomotopyNatIso_hom_natTrans :
    Functor.whiskerRight (NatTrans.mapHomotopyCategory α c) (e.extendHomotopyFunctor B) ≫
        (mapExtendHomotopyNatIso G e).hom =
      (mapExtendHomotopyNatIso F e).hom ≫
        Functor.whiskerLeft (e.extendHomotopyFunctor A) (NatTrans.mapHomotopyCategory α c') := by
  apply NatTrans.ext
  funext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.mapHomotopyCategory_app, HomotopyCategory.quotient_obj_as,
    mapExtendHomotopyNatIso_hom_app]
  exact ((HomotopyCategory.quotient B c').map_comp _ _).symm.trans
    ((congrArg (HomotopyCategory.quotient B c').map (mapExtendIso_hom_natTrans α e K)).trans
      ((HomotopyCategory.quotient B c').map_comp _ _))

end FunctorVariable

section Homology

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A] [CategoryWithHomology A]
  (e : c.Embedding c') {j : ι} {j' : ι'} (hj : e.f j = j')

/-- The homology of the extension by zero of `K` along `e`, in a degree hit by `e`, is the
homology of `K` in the corresponding degree, naturally in `K`. -/
noncomputable def extendHomologyNatIso :
    e.extendFunctor A ⋙ HomologicalComplex.homologyFunctor A c' j' ≅
      HomologicalComplex.homologyFunctor A c j :=
  NatIso.ofComponents (fun K ↦ K.extendHomologyIso e hj)
    (fun _ ↦ extendHomologyIso_hom_naturality _ _ hj)

variable [e.IsRelIff]

/-- `extendHomologyNatIso`, read on homotopy categories. -/
noncomputable def extendHomotopyHomologyNatIso :
    e.extendHomotopyFunctor A ⋙ HomotopyCategory.homologyFunctor A c' j' ≅
      HomotopyCategory.homologyFunctor A c j :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight (e.extendHomotopyFunctorFactors A)
        (HomotopyCategory.homologyFunctor A c' j') ≪≫
      Functor.isoWhiskerLeft (e.extendFunctor A)
        (HomotopyCategory.homologyFunctorFactors A c' j') ≪≫
      extendHomologyNatIso e hj ≪≫
      (HomotopyCategory.homologyFunctorFactors A c j).symm)

end Homology

end Stacks.DerivedIndexing
