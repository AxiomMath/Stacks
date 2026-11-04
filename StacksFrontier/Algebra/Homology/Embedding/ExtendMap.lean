module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Extending a complex commutes with applying a functor degreewise

Let `e : c.Embedding c'` be an embedding of complex shapes and let `F : C ⥤ D` be a functor
preserving zero morphisms between categories with zero objects. Extending a complex along `e`
inserts zero objects in the degrees outside the image of `e`, and `F` carries a zero object to a
zero object, so extending and applying `F` degreewise commute: the two complexes
`((F.mapHomologicalComplex c).obj K).extend e` and `(F.mapHomologicalComplex c').obj (K.extend e)`
are canonically isomorphic, by the identity in the degrees coming from `e` and by the unique map
between zero objects elsewhere.

## Main definitions

* `HomologicalComplex.extendMapXIso`: the degreewise comparison isomorphism, indexed by
  `Option ι` as `HomologicalComplex.extend.X` is.
* `HomologicalComplex.mapHomologicalComplexExtendIso`: the comparison isomorphism of complexes.

## Main results

* `HomologicalComplex.mapHomologicalComplexExtendIso_hom_f`: in a degree `i'` of the form
  `e.f i` the comparison isomorphism is the identity, read through the two canonical degree
  isomorphisms of the extensions.
* `HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality` and
  `HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality_functor`: the comparison
  isomorphism is natural in the complex and in the functor.
* `HomologicalComplex.mkHomFromSingle_comp_extendMap_mapHomologicalComplexExtendIso`: **a square
  of morphisms out of a complex concentrated in one degree is the square of its single
  component.** Given a morphism `φ : L ⟶ F(K)` of complexes over `c` and morphisms `b`, `b'`
  into the degree-`i` terms of `L` and of `K` out of objects `A`, `A'` related by
  `u : A ⟶ F(A')`, the square of complexes over `c'` formed by `u` in degree `i'`, by `b` and
  `b'` read into the extensions, and by `φ` extended, commutes as soon as the square of `u`,
  `b`, `b'` and the degree-`i` component of `φ` does.

## Implementation notes

The degreewise comparison is defined by matching on `Option ι` rather than by transporting along
an equality, so that it is the identity — not merely an `eqToHom` — in the degrees in the image
of `e`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- The degreewise comparison between the extension of `K` with `F` applied degreewise and `F`
applied degreewise to the extension of `K`: the identity on the degrees of `K`, and the unique
isomorphism of zero objects elsewhere. -/
noncomputable def extendMapXIso : ∀ i : Option ι,
    extend.X ((F.mapHomologicalComplex c).obj K) i ≅ F.obj (extend.X K i)
  | some _ => Iso.refl _
  | none => (extend.isZero_X ((F.mapHomologicalComplex c).obj K) rfl).iso
      (F.map_isZero (extend.isZero_X K rfl))

/-- In a degree of `K` the degreewise comparison is the identity, read through the two canonical
identifications of `HomologicalComplex.extend.X` with the term of the complex. -/
theorem extendMapXIso_hom_some {i : Option ι} {a : ι} (hi : i = some a) :
    (extendMapXIso F K i).hom =
      (extend.XIso ((F.mapHomologicalComplex c).obj K) hi).hom ≫
        F.map (extend.XIso K hi).inv := by
  subst hi
  dsimp only [extendMapXIso, extend.XIso, extend.X, Functor.mapHomologicalComplex, eqToIso,
    Iso.hom, Iso.inv]
  exact ((congrArg₂ (fun x y => x ≫ y) (eqToHom_refl (F.obj (K.X a)) _)
      ((congrArg F.map (eqToHom_refl (K.X a) _)).trans (F.map_id (K.X a)))).trans
    (Category.id_comp _)).symm

/-- The degreewise comparison commutes with the differentials of the two extensions. -/
theorem extendMapXIso_hom_d (i j : Option ι) :
    extend.d ((F.mapHomologicalComplex c).obj K) i j ≫ (extendMapXIso F K j).hom =
      (extendMapXIso F K i).hom ≫ F.map (extend.d K i j) := by
  match i, j with
  | none, _ => simp [extend.d_none_eq_zero _ _ _ rfl]
  | some _, none => simp [extend.d_none_eq_zero' _ _ _ rfl]
  | some a, some b =>
      show extend.d ((F.mapHomologicalComplex c).obj K) (some a) (some b) ≫
          (Iso.refl _).hom =
        (Iso.refl _).hom ≫ F.map (extend.d K (some a) (some b))
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Extending a complex along an embedding of complex shapes commutes with applying a
zero-morphism-preserving functor degreewise. -/
noncomputable def mapHomologicalComplexExtendIso (e : c.Embedding c') :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  Hom.isoOfComponents (fun i' => extendMapXIso F K (e.r i'))
    (fun _ _ _ => (extendMapXIso_hom_d F K _ _).symm)

/-- In a degree `i'` in the image of `e` the comparison isomorphism is the identity, read through
the canonical identifications of the two extensions with the term of `K` in degree `i`. -/
theorem mapHomologicalComplexExtendIso_hom_f (e : c.Embedding c') {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (mapHomologicalComplexExtendIso F K e).hom.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv :=
  extendMapXIso_hom_some F K (e.r_eq_some h)

/-- The comparison map of extensions attached to a morphism
`φ : L ⟶ (F.mapHomologicalComplex c).obj K` is, in a degree `i'` in the image of `e`, the
degree-`i` component of `φ` read through the two canonical degree isomorphisms. -/
theorem extendMap_mapHomologicalComplexExtendIso_f {L : HomologicalComplex D c}
    (φ : L ⟶ (F.mapHomologicalComplex c).obj K) (e : c.Embedding c') {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (extendMap φ e ≫ (mapHomologicalComplexExtendIso F K e).hom).f i' =
      (L.extendXIso e h).hom ≫ φ.f i ≫ F.map (K.extendXIso e h).inv := by
  rw [comp_f, extendMap_f _ _ h, mapHomologicalComplexExtendIso_hom_f _ _ _ h,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

/-- Two morphisms out of an extension agree once they agree in the degrees in the image of `e`. -/
private theorem extend_hom_ext {L : HomologicalComplex D c} {M : HomologicalComplex D c'}
    (e : c.Embedding c') {f g : L.extend e ⟶ M}
    (h : ∀ (a : ι) (i' : ι'), e.f a = i' → f.f i' = g.f i') : f = g := by
  ext i'
  cases hi : e.r i' with
  | none => exact (L.isZero_extend_X' e i' hi).eq_of_src _ _
  | some a => exact h a i' (e.f_eq_of_r_eq_some hi)

/-- The comparison isomorphism is natural in the complex: extending a morphism `f` and then
applying `F` degreewise agrees with applying `F` degreewise and then extending. -/
theorem mapHomologicalComplexExtendIso_inv_naturality {L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫
        (mapHomologicalComplexExtendIso F L e).inv =
      (mapHomologicalComplexExtendIso F K e).inv ≫
        extendMap ((F.mapHomologicalComplex c).map f) e := by
  rw [← cancel_epi (mapHomologicalComplexExtendIso F K e).hom, Iso.hom_inv_id_assoc,
    ← Category.assoc, Iso.comp_inv_eq]
  refine extend_hom_ext e fun a i' h => ?_
  rw [comp_f, comp_f, mapHomologicalComplexExtendIso_hom_f F K e h,
    mapHomologicalComplexExtendIso_hom_f F L e h,
    Functor.mapHomologicalComplex_map_f, extendMap_f f e h,
    extendMap_f ((F.mapHomologicalComplex c).map f) e h]
  simp [← Functor.map_comp]

/-- The comparison isomorphism is natural in the functor: a natural transformation `α : F ⟶ G`
applied degreewise to the extension of `K` agrees with the extension of `α` applied degreewise
to `K`. -/
theorem mapHomologicalComplexExtendIso_inv_naturality_functor {G : C ⥤ D}
    [G.PreservesZeroMorphisms] (α : F ⟶ G) (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫
        (mapHomologicalComplexExtendIso G K e).inv =
      (mapHomologicalComplexExtendIso F K e).inv ≫
        extendMap ((NatTrans.mapHomologicalComplex α c).app K) e := by
  rw [← cancel_epi (mapHomologicalComplexExtendIso F K e).hom, Iso.hom_inv_id_assoc,
    ← Category.assoc, Iso.comp_inv_eq]
  refine extend_hom_ext e fun a i' h => ?_
  rw [comp_f, comp_f, mapHomologicalComplexExtendIso_hom_f F K e h,
    mapHomologicalComplexExtendIso_hom_f G K e h,
    NatTrans.mapHomologicalComplex_app_f,
    extendMap_f ((NatTrans.mapHomologicalComplex α c).app K) e h]
  simp [α.naturality]

/-- **A square of morphisms out of a complex concentrated in one degree is the square of its
single component.** Let `φ : L ⟶ F(K)` be a morphism of complexes over `c`, let `b : A ⟶ L_i`
and `b' : A' ⟶ K_i` be morphisms out of objects related by `u : A ⟶ F(A')`, and suppose
`u ≫ F(b') = b ≫ φ_i`. Then the square of complexes over `c'` whose top arrow is `u` placed in
the degree `i' = e.f i`, whose vertical arrows are `b` and `b'` read into the extensions along
`e`, and whose bottom arrow is `φ` extended along `e`, commutes. -/
theorem mkHomFromSingle_comp_extendMap_mapHomologicalComplexExtendIso [DecidableEq ι']
    (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i')
    {L : HomologicalComplex D c} (φ : L ⟶ (F.mapHomologicalComplex c).obj K)
    {A : D} {A' : C} (u : A ⟶ F.obj A') (b : A ⟶ L.X i) (b' : A' ⟶ K.X i)
    (hu : ∀ k' : ι', c'.Rel i' k' →
      (u ≫ F.map (singleObjXSelf c' i' A').inv) ≫
        ((F.mapHomologicalComplex c').obj ((single C c' i').obj A')).d i' k' = 0)
    (hb : ∀ k' : ι', c'.Rel i' k' →
      (b ≫ (L.extendXIso e h).inv) ≫ (L.extend e).d i' k' = 0)
    (hb' : ∀ k' : ι', c'.Rel i' k' →
      (b' ≫ (K.extendXIso e h).inv) ≫ (K.extend e).d i' k' = 0)
    (hsq : u ≫ F.map b' = b ≫ φ.f i) :
    mkHomFromSingle (u ≫ F.map (singleObjXSelf c' i' A').inv) hu ≫
        (F.mapHomologicalComplex c').map
          (mkHomFromSingle (b' ≫ (K.extendXIso e h).inv) hb') =
      mkHomFromSingle (b ≫ (L.extendXIso e h).inv) hb ≫
        (extendMap φ e ≫ (mapHomologicalComplexExtendIso F K e).hom) := by
  refine from_single_hom_ext (j := i') ?_
  rw [comp_f, comp_f, mkHomFromSingle_f, mkHomFromSingle_f,
    Functor.mapHomologicalComplex_map_f, mkHomFromSingle_f,
    extendMap_mapHomologicalComplexExtendIso_f F K φ e h,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, CategoryTheory.Iso.map_inv_hom_id_assoc,
    CategoryTheory.Iso.inv_hom_id_assoc]
  rw [reassoc_of% hsq]

end HomologicalComplex

end
