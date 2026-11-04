module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Homology of the Čech nerve of a locally surjective morphism of presheaves of sets

Let `C` be a site, `J` a Grothendieck topology on it, and `f : F ⟶ G` a morphism of presheaves
of sets on `C` which is *locally surjective*, i.e. surjective after sheafification.  Let `K` be
the simplicial presheaf whose `n`-th term is the `(n + 1)`-st fibre product of `F` over `G`,
that is Mathlib's `CategoryTheory.Arrow.cechNerve`.  Applying the free abelian sheaf functor
degreewise and taking the associated alternating face map complex gives the homology sheaves
`H_n(K)`.  This file proves that `H_n(K) = 0` for `n > 0` and that the augmentation identifies
`H_0(K)` with the free abelian sheaf `**Z**_G^♯` on the target.

## Main definitions

* `CategoryTheory.Presheaf.freeAbelian` and `CategoryTheory.Presheaf.freeAbelianSheaf` are the
  free abelian presheaf and free abelian sheaf functors `ℱ ↦ **Z**_ℱ`, `ℱ ↦ **Z**_ℱ^♯`, together
  with their adjunctions `CategoryTheory.Presheaf.freeAbelianAdj`,
  `CategoryTheory.Presheaf.freeAbelianSheafAdj`.
* `CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor`,
  `CategoryTheory.SimplicialObject.sheafHomologyFunctor` and
  `CategoryTheory.SimplicialObject.sheafHomology` are the complex `s(**Z**_K^♯)` of a simplicial
  presheaf of sets and its homology sheaves (Stacks Project, Tag 01GB).
* `CategoryTheory.Presheaf.cechNerveSheafAugmentation` is the augmentation of that complex for
  a Čech nerve, and `CategoryTheory.Presheaf.cechNerveSheafHomologyZeroAugmentation` is the
  induced map out of degree-zero homology.
* `CategoryTheory.Limits.isLimitMapWidePullbackCone`,
  `CategoryTheory.Arrow.cechNerveComp` and `CategoryTheory.Arrow.augmentedCechNerveComp`
  record that a functor preserving the relevant wide pullbacks commutes with the (augmented)
  Čech nerve; `CategoryTheory.Arrow.cechNerveCompMonoIso` records that composing with a
  monomorphism does not change the Čech nerve.
* `AlgebraicTopology.AlternatingFaceMapComplex.arrowMkεIsoOfIso` and
  `AlgebraicTopology.AlternatingFaceMapComplex.arrowMkεMapIso` transport the augmentation `ε`
  along an isomorphism of augmented simplicial objects, resp. along an additive functor.

## Main results

* `CategoryTheory.Presheaf.isZero_sheafHomology_cechNerve_of_isLocallySurjective`: the homology
  sheaves of the Čech nerve vanish in positive degrees.
* `CategoryTheory.Presheaf.isIso_cechNerveSheafHomologyZeroAugmentation`: in degree zero the
  augmentation induces an isomorphism onto `**Z**_G^♯`.
* `CategoryTheory.Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective`: the
  same degree-zero statement for the other presentation of the canonical map out of degree-zero
  homology, namely `HomologicalComplex.homologyι` followed by the descent of the degree-zero
  augmentation through `HomologicalComplex.opcycles`; the two presentations are identified by
  `CategoryTheory.Presheaf.cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles`.
* `CategoryTheory.Presheaf.quasiIso_cechNerveSheafAugmentation`: the augmentation of
  `s(**Z**_K^♯)` towards the complex concentrated in degree zero on `**Z**_G^♯` is a
  quasi-isomorphism.
* `CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`: the free abelian sheaf functor
  inverts the morphisms of presheaves of sets which become isomorphisms after sheafification.
* `CategoryTheory.Presheaf.W_range_ι_of_isLocallySurjective`: for a locally surjective `f`, the
  inclusion of the image subpresheaf becomes an isomorphism after sheafification.

## Implementation notes

The universe `w` of the presheaves of sets is kept independent of the universes `u`, `v` of the
site: nothing here fixes `w = max u v`.  Consequently the sheafification of *type*-valued
presheaves is never used (Mathlib only provides it for `Type (max u v)`); the only sheafification
hypothesis is the one the statement needs, `HasSheafify J AddCommGrpCat.{w}`, and it already
carries left exactness of `presheafToSheaf` as part of its definition, which is what makes the
comparison between presheaf homology and sheaf homology work.

Degree-zero homology is identified with `**Z**_G^♯` by `HomologicalComplex.homologyMap` of the
augmentation followed by `HomologicalComplex.singleObjHomologySelfIso`, because that form makes
the comparison with the quasi-isomorphism statement immediate.  The alternative presentation,
`HomologicalComplex.homologyι` followed by a `HomologicalComplex.descOpcycles` out of
`HomologicalComplex.opcycles`, is proved equal to it in
`cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles`.

In that comparison the degree-zero augmentation is taken as a *variable* `k` together with a
hypothesis `hk` pinning it down, rather than written out.  This is forced, not cosmetic: the
spelled-out term `(freeAbelianSheaf J).map (WidePullback.base _)` only has the type required of
an argument of `descOpcycles` after semireducible unfolding of
`SimplicialObject.freeAbelianSheafComplexFunctor`, so every `rw` whose motive abstracts it is
rejected by the type-correctness check at `implicit` transparency.  With `k` a local hypothesis
all the intermediate terms are typed syntactically as required.  For the same reason `hk` is
stated as an equation of morphisms into `**Z**_G^♯` itself —
postcomposed with `HomologicalComplex.singleObjXSelf` — rather than into the degree-zero term of
the complex concentrated there.

## References

* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w' w v' v u' u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- If `F` preserves the wide pullback of a family `f`, then the image under `F` of the
wide pullback cone of `f` is a limit cone. -/
noncomputable def isLimitMapWidePullbackCone (F : C ⥤ D) {ι : Type t} {X : C} {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [HasWidePullback X Y f]
    [PreservesLimit (WidePullbackShape.wideCospan X Y f) F] :
    IsLimit (WidePullbackCone.mk (f := fun i ↦ F.map (f i)) (F.map (WidePullback.base f))
      (fun i ↦ F.map (WidePullback.π f i)) (fun i ↦ by rw [← F.map_comp]; simp)) := by
  have h : IsLimit (F.mapCone (limit.cone (WidePullbackShape.wideCospan X Y f))) :=
    isLimitOfPreserves F (limit.isLimit _)
  exact WidePullbackCone.IsLimit.mk _
    (fun t ↦ h.lift (WidePullbackShape.mkCone t.base t.π (fun j ↦ t.condition j)))
    (fun _ ↦ h.fac _ none) (fun _ i ↦ h.fac _ (some i))
    (fun t m hb hπ ↦ h.uniq (WidePullbackShape.mkCone t.base t.π (fun j ↦ t.condition j)) m
      (by rintro (_ | j); exacts [hb, hπ j]))

end CategoryTheory.Limits

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
  {D : Type u'} [Category.{v'} D] [HasFiniteWidePullbacks D]
  (F : C ⥤ D) (a : Arrow C)
  [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) F]

/-- The comparison isomorphism in degree `n` between the image under `F` of the Čech nerve of
an arrow `a` and the Čech nerve of the image arrow. -/
noncomputable def cechNerveCompIsoApp (n : SimplexCategoryᵒᵖ) :
    F.obj (a.cechNerve.obj n) ≅ (Arrow.mk (F.map a.hom)).cechNerve.obj n :=
  (isLimitMapWidePullbackCone F (fun _ : Fin (n.unop.len + 1) ↦ a.hom)).conePointUniqueUpToIso
    (limit.isLimit _)

/-- The comparison isomorphism `cechNerveCompIsoApp` followed by the `i`-th projection is the
image under `F` of the `i`-th projection. -/
@[reassoc (attr := simp)]
lemma cechNerveCompIsoApp_hom_comp_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    (cechNerveCompIsoApp F a n).hom ≫ WidePullback.π (fun _ ↦ F.map a.hom) i =
      F.map (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ a.hom) i) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitMapWidePullbackCone F (fun _ : Fin (n.unop.len + 1) ↦ a.hom)) (limit.isLimit _) (some i)

/-- The comparison isomorphism `cechNerveCompIsoApp` followed by the base projection is the
image under `F` of the base projection. -/
@[reassoc (attr := simp)]
lemma cechNerveCompIsoApp_hom_comp_base (n : SimplexCategoryᵒᵖ) :
    (cechNerveCompIsoApp F a n).hom ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦
        F.map a.hom) =
      F.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ a.hom)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitMapWidePullbackCone F (fun _ : Fin (n.unop.len + 1) ↦ a.hom)) (limit.isLimit _) none

/-- The Čech nerve construction commutes with a functor preserving the relevant wide
pullbacks. -/
noncomputable def cechNerveComp : a.cechNerve ⋙ F ≅ (Arrow.mk (F.map a.hom)).cechNerve :=
  NatIso.ofComponents (cechNerveCompIsoApp F a) (fun {n m} g ↦ by
    apply WidePullback.hom_ext
    · intro j
      simp only [Functor.comp_map, Category.assoc, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
        Arrow.cechNerve_map, cechNerveCompIsoApp_hom_comp_π, ← Functor.map_comp,
        WidePullback.lift_π]
    · simp only [Functor.comp_map, Category.assoc, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
        Arrow.cechNerve_map, cechNerveCompIsoApp_hom_comp_base, ← Functor.map_comp,
        WidePullback.lift_base])

/-- The augmented Čech nerve construction commutes with a functor preserving the relevant
wide pullbacks. -/
noncomputable def augmentedCechNerveComp :
    ((SimplicialObject.Augmented.whiskering C D).obj F).obj a.augmentedCechNerve ≅
      (Arrow.mk (F.map a.hom)).augmentedCechNerve :=
  Comma.isoMk (cechNerveComp F a) (Iso.refl _) (by
    ext n
    refine (cechNerveCompIsoApp_hom_comp_base F a n).trans ?_
    simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
      SimplicialObject.const, NatTrans.comp_app, Functor.whiskerRight_app,
      Arrow.augmentedCechNerve_hom_app]
    exact Eq.symm (Eq.trans (Category.comp_id _) (Category.comp_id _)))

end CategoryTheory.Arrow

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The free abelian presheaf functor `ℱ ↦ **Z**_ℱ`: apply the free abelian group functor
sectionwise. -/
noncomputable abbrev freeAbelian : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (Functor.whiskeringRight Cᵒᵖ (Type w) AddCommGrpCat.{w}).obj AddCommGrpCat.free

/-- The underlying presheaf of sets of a presheaf of abelian groups. -/
@[sga "4 I 5.8.0" "special case"]
noncomputable abbrev forgetAbelian : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ (Cᵒᵖ ⥤ Type w) :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{w} (Type w)).obj (forget AddCommGrpCat.{w})

/-- The free abelian presheaf functor is left adjoint to the underlying-presheaf-of-sets
functor. -/
@[sga "4 I 5.8.2" "special case"]
noncomputable def freeAbelianAdj :
    (freeAbelian : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})) ⊣ forgetAbelian :=
  AddCommGrpCat.adj.whiskerRight Cᵒᵖ

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The free abelian sheaf functor `ℱ ↦ **Z**_ℱ^♯`. -/
noncomputable def freeAbelianSheaf : (Cᵒᵖ ⥤ Type w) ⥤ Sheaf J AddCommGrpCat.{w} :=
  freeAbelian ⋙ presheafToSheaf J AddCommGrpCat.{w}

/-- The free abelian sheaf functor is left adjoint to the functor taking a sheaf of abelian
groups to its underlying presheaf of sets. -/
noncomputable def freeAbelianSheafAdj :
    freeAbelianSheaf.{w} J ⊣ sheafToPresheaf J AddCommGrpCat.{w} ⋙ forgetAbelian :=
  freeAbelianAdj.comp (sheafificationAdjunction J AddCommGrpCat.{w})

/-- The free abelian sheaf functor inverts the morphisms of presheaves of sets which become
isomorphisms after sheafification. -/
lemma isIso_freeAbelianSheaf_map_of_W {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) (hf : J.W f) :
    IsIso ((freeAbelianSheaf J).map f) := by
  refine isIso_of_coyoneda_map_bijective _ (fun S ↦ ?_)
  have hS : IsSheaf J ((sheafToPresheaf J AddCommGrpCat.{w} ⋙ forgetAbelian).obj S) :=
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj S).property
  have key : (fun (g : (freeAbelianSheaf J).obj G ⟶ S) ↦ (freeAbelianSheaf J).map f ≫ g) =
      ((freeAbelianSheafAdj J).homEquiv F S).symm ∘ (fun h ↦ f ≫ h) ∘
        ((freeAbelianSheafAdj J).homEquiv G S) := by
    funext g
    simp only [Function.comp_apply, ← (freeAbelianSheafAdj J).homEquiv_naturality_left,
      Equiv.symm_apply_apply]
  rw [key]
  exact ((freeAbelianSheafAdj J).homEquiv F S).symm.bijective.comp
    ((hf _ hS).comp ((freeAbelianSheafAdj J).homEquiv G S).bijective)

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- If `f` is locally surjective, the inclusion of its image subpresheaf becomes an
isomorphism after sheafification. -/
lemma W_range_ι_of_isLocallySurjective {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G)
    [IsLocallySurjective J f] : J.W (Subfunctor.range f).ι := by
  have htop : (Subfunctor.range f).sheafify J = ⊤ :=
    (isLocallySurjective_iff_range_sheafify_eq_top' J f).1 inferInstance
  have hiso : IsIso ((Subfunctor.range f).sheafify J).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 htop
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  have key : Subfunctor.homOfLe ((Subfunctor.range f).le_sheafify J) ≫
      ((Subfunctor.range f).sheafify J).ι = (Subfunctor.range f).ι := Subfunctor.homOfLe_ι _
  constructor
  · intro g₁ g₂ hg
    replace hg : (Subfunctor.range f).ι ≫ g₁ = (Subfunctor.range f).ι ≫ g₂ := hg
    rw [← cancel_epi (((Subfunctor.range f).sheafify J).ι)]
    refine (Subfunctor.range f).to_sheafify_lift_unique hZ _ _ ?_
    rw [reassoc_of% key, reassoc_of% key]
    exact hg
  · intro g
    refine ⟨inv (((Subfunctor.range f).sheafify J).ι) ≫
      (Subfunctor.range f).sheafifyLift g hZ, ?_⟩
    show (Subfunctor.range f).ι ≫ _ = g
    rw [← key, Category.assoc, IsIso.hom_inv_id_assoc]
    exact (Subfunctor.range f).to_sheafifyLift g hZ

end CategoryTheory.Presheaf

namespace AlgebraicTopology.AlternatingFaceMapComplex

open SimplicialObject SimplicialObject.Augmented

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  {B : Type u'} [Category.{v'} B] [Preadditive B] [HasZeroObject B]

/-- The augmentation of the alternating face map complex, transported along an isomorphism
of augmented simplicial objects. -/
noncomputable def arrowMkεIsoOfIso {Z₁ Z₂ : SimplicialObject.Augmented A} (φ : Z₁ ≅ Z₂) :
    Arrow.mk (ε.app Z₁) ≅ Arrow.mk (ε.app Z₂) :=
  Arrow.isoMk ((Augmented.drop ⋙ alternatingFaceMapComplex A).mapIso φ)
    ((Augmented.point ⋙ ChainComplex.single₀ A).mapIso φ) (ε.naturality φ.hom)

variable (E : A ⥤ B) [E.Additive]

/-- The comparison isomorphism of alternating face map complexes and the isomorphism of single
complexes intertwine the image under `E` of the augmentation of `Z` with the augmentation of
the image of `Z` under `E`. -/
lemma arrowMkεMapIso_w (Z : SimplicialObject.Augmented A) :
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso E).app Z.left).hom ≫
        ε.app (((Augmented.whiskering A B).obj E).obj Z) =
      (E.mapHomologicalComplex (ComplexShape.down ℕ)).map (ε.app Z) ≫
        ((HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.down ℕ) 0).app
          Z.right).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp [alternatingFaceMapComplexCompMapHomologicalComplexIso,
    SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]

/-- The augmentation of the alternating face map complex is compatible with applying an
additive functor degreewise. -/
noncomputable def arrowMkεMapIso (Z : SimplicialObject.Augmented A) :
    Arrow.mk ((E.mapHomologicalComplex (ComplexShape.down ℕ)).map (ε.app Z)) ≅
      Arrow.mk (ε.app (((Augmented.whiskering A B).obj E).obj Z)) :=
  Arrow.isoMk ((alternatingFaceMapComplexCompMapHomologicalComplexIso E).app Z.left)
    ((HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.down ℕ) 0).app Z.right)
    (arrowMkεMapIso_w E Z)

/-- For a surjection of types, the augmentation of the alternating face map complex of the
degreewise free abelian group on the augmented Čech nerve is a quasi-isomorphism. -/
lemma quasiIso_ε_app_free_augmentedCechNerve {X Y : Type w} (p : X ⟶ Y)
    (hp : Function.Surjective p) :
    QuasiIso (ε.app (((Augmented.whiskering (Type w) AddCommGrpCat.{w}).obj
      AddCommGrpCat.free).obj (Arrow.mk p).augmentedCechNerve)) := by
  have S : SplitEpi p := ⟨↾Function.surjInv hp, by ext y; exact Function.surjInv_eq hp y⟩
  exact inferInstanceAs (QuasiIso
    ((((Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk p) S).map
      AddCommGrpCat.free).homotopyEquiv).hom))

end AlgebraicTopology.AlternatingFaceMapComplex

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
  {X Y' Y : C} (g : X ⟶ Y') (m : Y' ⟶ Y) [Mono m]

/-- The comparison map from the Čech nerve of `g` to the Čech nerve of `g ≫ m`, in degree
`n`. -/
noncomputable def cechNerveCompMonoHom (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk g).cechNerve.obj n ⟶ (Arrow.mk (g ≫ m)).cechNerve.obj n :=
  WidePullback.lift (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g) ≫ m)
    (fun i ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g) i)
    (fun i ↦ by
      simp only [Arrow.mk_hom]
      rw [← Category.assoc, WidePullback.π_arrow])

/-- The inverse comparison map, available because `m` is a monomorphism. -/
noncomputable def cechNerveCompMonoInv (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk (g ≫ m)).cechNerve.obj n ⟶ (Arrow.mk g).cechNerve.obj n :=
  WidePullback.lift (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g ≫ m) 0 ≫ g)
    (fun i ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g ≫ m) i)
    (fun i ↦ by
      simp only [Arrow.mk_hom]
      rw [← cancel_mono m, Category.assoc, Category.assoc, WidePullback.π_arrow,
        WidePullback.π_arrow])

omit [Mono m] in
/-- The map `cechNerveCompMonoHom` followed by the `i`-th projection is the `i`-th projection. -/
@[reassoc (attr := simp)]
lemma cechNerveCompMonoHom_comp_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    cechNerveCompMonoHom g m n ≫ WidePullback.π (fun _ ↦ g ≫ m) i =
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g) i :=
  WidePullback.lift_π _ _ _ _ i

omit [Mono m] in
/-- The map `cechNerveCompMonoHom` followed by the base projection is the base projection
followed by `m`. -/
@[reassoc (attr := simp)]
lemma cechNerveCompMonoHom_comp_base (n : SimplexCategoryᵒᵖ) :
    cechNerveCompMonoHom g m n ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g ≫ m) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g) ≫ m :=
  WidePullback.lift_base _ _ _ _

/-- The map `cechNerveCompMonoInv` followed by the `i`-th projection is the `i`-th projection. -/
@[reassoc (attr := simp)]
lemma cechNerveCompMonoInv_comp_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    cechNerveCompMonoInv g m n ≫ WidePullback.π (fun _ ↦ g) i =
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g ≫ m) i :=
  WidePullback.lift_π _ _ _ _ i

/-- The map `cechNerveCompMonoInv` followed by the base projection is the `0`-th projection
followed by `g`. -/
@[reassoc (attr := simp)]
lemma cechNerveCompMonoInv_comp_base (n : SimplexCategoryᵒᵖ) :
    cechNerveCompMonoInv g m n ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g) =
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g ≫ m) 0 ≫ g :=
  WidePullback.lift_base _ _ _ _

/-- The degree-`n` component of `CategoryTheory.Arrow.cechNerveCompMonoIso`. -/
noncomputable def cechNerveCompMonoIsoApp (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk g).cechNerve.obj n ≅ (Arrow.mk (g ≫ m)).cechNerve.obj n where
  hom := cechNerveCompMonoHom g m n
  inv := cechNerveCompMonoInv g m n
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      simp
    · simp [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right]
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      simp
    · simp [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right]

/-- Composing with a monomorphism does not change the Čech nerve. -/
noncomputable def cechNerveCompMonoIso :
    (Arrow.mk g).cechNerve ≅ (Arrow.mk (g ≫ m)).cechNerve :=
  NatIso.ofComponents (cechNerveCompMonoIsoApp g m) (fun {n p} h ↦ by
    apply WidePullback.hom_ext
    · intro j
      simp [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, cechNerveCompMonoIsoApp,
        WidePullback.lift_π]
    · simp [Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, cechNerveCompMonoIsoApp,
        WidePullback.lift_base, WidePullback.lift_base_assoc])

end CategoryTheory.Arrow

namespace CategoryTheory

open AlgebraicTopology _root_.CategoryTheory.SimplicialObject
  _root_.CategoryTheory.SimplicialObject.Augmented

namespace SimplicialObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The complex `s(**Z**_K^♯)` of free abelian sheaves attached to a simplicial presheaf of
sets `K`. -/
@[sga "4 V 7.2.0" "special case"]
noncomputable def freeAbelianSheafComplexFunctor :
    SimplicialObject (Cᵒᵖ ⥤ Type w) ⥤ ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ :=
  (SimplicialObject.whiskering _ _).obj (Presheaf.freeAbelianSheaf J) ⋙
    alternatingFaceMapComplex _

/-- The degree-`n` homology sheaf functor on simplicial presheaves of sets. -/
noncomputable def sheafHomologyFunctor (n : ℕ) :
    SimplicialObject (Cᵒᵖ ⥤ Type w) ⥤ Sheaf J AddCommGrpCat.{w} :=
  freeAbelianSheafComplexFunctor J ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The degree-`n` homology sheaf `H_n(K)` of a simplicial presheaf of sets. -/
@[sga "4 V 7.2.0" "H_i(K), M = Z_E"]
noncomputable abbrev sheafHomology (K : SimplicialObject (Cᵒᵖ ⥤ Type w)) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} := (sheafHomologyFunctor J n).obj K

end SimplicialObject

namespace Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] {F G : Cᵒᵖ ⥤ Type w}

/-- For a presheaf morphism which is surjective on each object, the augmentation of the free
abelian presheaf complex of its Čech nerve is a quasi-isomorphism. -/
lemma quasiIso_ε_freeAbelian_augmentedCechNerve (e : F ⟶ G)
    (he : ∀ U, Function.Surjective (e.app U)) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Cᵒᵖ ⥤ AddCommGrpCat.{w})).obj freeAbelian).obj
        (Arrow.mk e).augmentedCechNerve)) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro U
  have Ψ : ((Augmented.whiskering (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w}).obj
        ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)).obj
        (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Cᵒᵖ ⥤ AddCommGrpCat.{w})).obj freeAbelian).obj
          (Arrow.mk e).augmentedCechNerve) ≅
      ((Augmented.whiskering (Type w) AddCommGrpCat.{w}).obj AddCommGrpCat.free).obj
        (Arrow.mk (e.app U)).augmentedCechNerve :=
    ((Augmented.whiskering (Type w) AddCommGrpCat.{w}).obj AddCommGrpCat.free).mapIso
      (Arrow.augmentedCechNerveComp ((evaluation Cᵒᵖ (Type w)).obj U) (Arrow.mk e))
  refine (_root_.quasiIso_iff_of_arrow_mk_iso _ _
    ((AlternatingFaceMapComplex.arrowMkεMapIso ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)
      _).trans (AlternatingFaceMapComplex.arrowMkεIsoOfIso Ψ))).2 ?_
  exact AlternatingFaceMapComplex.quasiIso_ε_app_free_augmentedCechNerve _ (he U)

/-- The sheafified form of `quasiIso_ε_freeAbelian_augmentedCechNerve`. -/
lemma quasiIso_ε_freeAbelianSheaf_augmentedCechNerve (e : F ⟶ G)
    (he : ∀ U, Function.Surjective (e.app U)) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
        (freeAbelianSheaf J)).obj (Arrow.mk e).augmentedCechNerve)) := by
  have : (presheafToSheaf J AddCommGrpCat.{w}).PreservesHomology := inferInstance
  have := quasiIso_ε_freeAbelian_augmentedCechNerve e he
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (AlternatingFaceMapComplex.arrowMkεMapIso (presheafToSheaf J AddCommGrpCat.{w})
      (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Cᵒᵖ ⥤ AddCommGrpCat.{w})).obj freeAbelian).obj
        (Arrow.mk e).augmentedCechNerve))).1
    (HomologicalComplex.quasiIso_map_of_preservesHomology _ _)

variable (f : F ⟶ G)

/-- The augmentation of the free abelian sheaf complex of the Čech nerve of `f`. -/
noncomputable def cechNerveSheafAugmentation :
    (SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f).cechNerve ⟶
      (ChainComplex.single₀ (Sheaf J AddCommGrpCat.{w})).obj ((freeAbelianSheaf J).obj G) :=
  AlternatingFaceMapComplex.ε.app
    (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
      (freeAbelianSheaf J)).obj (Arrow.mk f).augmentedCechNerve)

/-- **Stacks Project, Tag 01GC.** If `f` is locally surjective, the augmentation of the free
abelian sheaf complex of its Čech nerve is a quasi-isomorphism. -/
lemma quasiIso_cechNerveSheafAugmentation (hf : IsLocallySurjective J f) :
    QuasiIso (cechNerveSheafAugmentation J f) := by
  have := hf
  have hsurj : ∀ U, Function.Surjective ((Subfunctor.toRange f).app U) := by
    rintro U ⟨y, x, rfl⟩
    exact ⟨x, Subtype.ext (Subfunctor.toRange_app_val f x)⟩
  have hleft : IsIso (((SimplicialObject.whiskering (Cᵒᵖ ⥤ Type w)
      (Sheaf J AddCommGrpCat.{w})).obj (freeAbelianSheaf J)).map
        (Arrow.cechNerveCompMonoIso (Subfunctor.toRange f) (Subfunctor.range f).ι).hom) :=
    inferInstance
  have hright : IsIso ((freeAbelianSheaf J).map (Subfunctor.range f).ι) :=
    isIso_freeAbelianSheaf_map_of_W J _ (W_range_ι_of_isLocallySurjective J f)
  let ψ : (Arrow.mk (Subfunctor.toRange f)).augmentedCechNerve ⟶
      (Arrow.mk f).augmentedCechNerve :=
    { left := (Arrow.cechNerveCompMonoIso (Subfunctor.toRange f) (Subfunctor.range f).ι).hom
      right := (Subfunctor.range f).ι
      w := NatTrans.ext (funext fun n ↦
        Arrow.cechNerveCompMonoHom_comp_base (Subfunctor.toRange f)
          (Subfunctor.range f).ι n) }
  let Φiso : ((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
        (freeAbelianSheaf J)).obj (Arrow.mk (Subfunctor.toRange f)).augmentedCechNerve ≅
      ((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
        (freeAbelianSheaf J)).obj (Arrow.mk f).augmentedCechNerve :=
    Comma.isoMk (@asIso _ _ _ _ _ hleft) (@asIso _ _ _ _ _ hright) (by
      exact (((Augmented.whiskering (Cᵒᵖ ⥤ Type w) (Sheaf J AddCommGrpCat.{w})).obj
        (freeAbelianSheaf J)).map ψ).w)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (AlternatingFaceMapComplex.arrowMkεIsoOfIso Φiso)).1
    (quasiIso_ε_freeAbelianSheaf_augmentedCechNerve J (Subfunctor.toRange f) hsurj)

/-- For a locally surjective `f`, the augmentation induces isomorphisms on homology. -/
private lemma isIso_homologyMap_cechNerveSheafAugmentation (hf : IsLocallySurjective J f)
    (n : ℕ) : IsIso (HomologicalComplex.homologyMap (cechNerveSheafAugmentation J f) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).1
    ((quasiIso_cechNerveSheafAugmentation J f hf).quasiIsoAt n)

/-- The positive homology sheaves of the Čech nerve of a locally surjective morphism of
presheaves of sets vanish. -/
@[stacks 01GC "positive degrees"]
lemma isZero_sheafHomology_cechNerve_of_isLocallySurjective (hf : IsLocallySurjective J f)
    (n : ℕ) (hn : 0 < n) :
    IsZero (SimplicialObject.sheafHomology J (Arrow.mk f).cechNerve n) := by
  have hn' := isIso_homologyMap_cechNerveSheafAugmentation J f hf n
  exact (HomologicalComplex.isZero_single_obj_homology _ _ _ n (by omega)).of_iso
    (@asIso _ _ _ _ _ hn')

/-- The canonical map from the degree-zero homology sheaf of the Čech nerve of `f` to the free
abelian sheaf on the target, induced by the augmentation. -/
noncomputable def cechNerveSheafHomologyZeroAugmentation :
    SimplicialObject.sheafHomology J (Arrow.mk f).cechNerve 0 ⟶ (freeAbelianSheaf J).obj G :=
  HomologicalComplex.homologyMap (cechNerveSheafAugmentation J f) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom

/-- The augmentation of the Čech nerve of a locally surjective morphism induces an isomorphism
from its degree-zero homology sheaf to the free abelian sheaf on the target. -/
@[stacks 01GC "degree zero"]
lemma isIso_cechNerveSheafHomologyZeroAugmentation (hf : IsLocallySurjective J f) :
    IsIso (cechNerveSheafHomologyZeroAugmentation J f) := by
  have h0 := isIso_homologyMap_cechNerveSheafAugmentation J f hf 0
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 (Iso.isIso_hom _)

/-- The degree-zero component of the augmentation `cechNerveSheafAugmentation`, read as a
morphism to `**Z**_G^♯` itself rather than to the degree-zero term of the complex concentrated
there, is the free abelian sheaf functor applied to the base map of the wide pullback. -/
lemma cechNerveSheafAugmentation_f_zero_comp_singleObjXSelf_hom :
    (cechNerveSheafAugmentation J f).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          ((freeAbelianSheaf J).obj G)).hom =
      (freeAbelianSheaf J).map (WidePullback.base fun _ ↦ f) := by
  rw [cechNerveSheafAugmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
    NatTrans.comp_app, Functor.whiskerRight_app, ChainComplex.single₀ObjXSelf, Iso.refl_hom,
    Category.comp_id, Functor.constComp_hom_app]
  exact Category.comp_id _

/-- The degree-zero augmentation annihilates every incoming differential of the free abelian
sheaf complex of the Čech nerve, hence descends through `opcycles`. -/
lemma d_comp_cechNerveSheafAugmentation_f_zero
    {k : ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f).cechNerve).X 0 ⟶
      (freeAbelianSheaf J).obj G}
    (hk : (cechNerveSheafAugmentation J f).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        ((freeAbelianSheaf J).obj G)).hom = k) (j : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f).cechNerve).d j 0 ≫
      k = 0 := by
  rw [← hk, ← Category.assoc, ← (cechNerveSheafAugmentation J f).comm j 0,
    HomologicalComplex.single_obj_d, comp_zero, zero_comp]

/-- `cechNerveSheafHomologyZeroAugmentation` is the map out of degree-zero homology obtained by
descending the degree-zero augmentation `k` through `opcycles` and restricting along
`homologyι`. -/
lemma cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles
    {k : ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f).cechNerve).X 0 ⟶
      (freeAbelianSheaf J).obj G}
    (hk : (cechNerveSheafAugmentation J f).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        ((freeAbelianSheaf J).obj G)).hom = k) (j : ℕ)
    (hj : (ComplexShape.down ℕ).prev 0 = j)
    (hk₀ : ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk f).cechNerve).d j 0 ≫ k = 0) :
    cechNerveSheafHomologyZeroAugmentation J f =
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f).cechNerve).homologyι 0 ≫
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f).cechNerve).descOpcycles k j hj hk₀ := by
  have key : HomologicalComplex.opcyclesMap (cechNerveSheafAugmentation J f) 0 ≫
      (HomologicalComplex.singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0
        ((freeAbelianSheaf J).obj G)).inv =
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk f).cechNerve).descOpcycles k j hj hk₀ := by
    rw [← cancel_epi (HomologicalComplex.pOpcycles _ 0),
      HomologicalComplex.p_opcyclesMap_assoc,
      HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv,
      HomologicalComplex.p_descOpcycles]
    exact hk
  show HomologicalComplex.homologyMap (cechNerveSheafAugmentation J f) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
        ((freeAbelianSheaf J).obj G)).hom = _
  rw [← HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv,
    HomologicalComplex.homologyι_naturality_assoc, key]

/-- **Stacks Project, Tag 01GC (degree zero).** For a locally surjective `f`, the descent of
the degree-zero augmentation through `opcycles`, restricted along `homologyι`, is an
isomorphism from the degree-zero homology sheaf of the Čech nerve onto `**Z**_G^♯`. -/
lemma isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective
    (hf : IsLocallySurjective J f)
    {k : ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk f).cechNerve).X 0 ⟶
      (freeAbelianSheaf J).obj G}
    (hk : (cechNerveSheafAugmentation J f).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        ((freeAbelianSheaf J).obj G)).hom = k) (j : ℕ)
    (hj : (ComplexShape.down ℕ).prev 0 = j)
    (hk₀ : ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk f).cechNerve).d j 0 ≫ k = 0) :
    IsIso (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f).cechNerve).homologyι 0 ≫
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk f).cechNerve).descOpcycles k j hj hk₀) := by
  have h := isIso_cechNerveSheafHomologyZeroAugmentation J f hf
  rwa [cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles J f hk j hj hk₀] at h

end Presheaf

end CategoryTheory
