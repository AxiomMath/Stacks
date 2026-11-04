module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatQuasiFiniteDescent

/-!
# Finite étale covers of a pushout along a closed immersion and an integral morphism

Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an integral morphism satisfying the
fibrewise affineness condition of [Stacks Project, Tag 0ECI], so that the pushout `Y ⨿_Z X`
exists.  This file assembles the two sides of the comparison between the finite étale covers of
`Y ⨿_Z X` and pairs of finite étale covers of `Y` and of `X` glued over `Z`.

A *finite étale cartesian triple* is a cartesian diagram over the pushout situation whose three
vertical morphisms are finite étale.  Such a triple is sent on the one hand to its pushout, a
finite étale cover of `Y ⨿_Z X`, and on the other hand to the pair of its covers of `Y` and of
`X` together with the canonical identification of their restrictions to `Z`, that is to an
object of the 2-fibre product of categories `FÉt_Y ×_{FÉt_Z} FÉt_X`.  Mathlib's model of that
2-fibre product is `CategoryTheory.Limits.CategoricalPullback`.

That the pushout of a finite étale triple is again finite étale is the geometric input of
[Stacks Project, Tag 0EK4]: the morphism of pushouts is separated, locally of finite type and
locally quasi-finite by [Stacks Project, Tag 0ECK], it is étale by
[Stacks Project, Tag 0ECL], and it is universally closed because its two restrictions to the
constituents of the upper pushout are composites of a finite morphism with an integral one and
the two canonical morphisms into a pushout are jointly surjective.  Being proper and locally
quasi-finite it is finite.

The first of the two functors is an equivalence: it is faithful and full because the pushout
construction is fully faithful on morphisms of cartesian diagrams, and essentially surjective
because every finite étale cover of the pushout is the pushout of its two base changes, by
[Stacks Project, Tag 0ECL].

## Main definitions

* `AlgebraicGeometry.FiniteEtaleCartesianTriple` — the cartesian diagrams over a pushout
  situation whose three vertical morphisms are finite étale.
* `AlgebraicGeometry.finiteEtaleTripleToOver` — the pushout of a finite étale triple, as a
  finite étale cover of `Y ⨿_Z X`.
* `AlgebraicGeometry.finiteEtaleTripleToCategoricalPullback` — a finite étale triple, read as an
  object of the 2-fibre product `FÉt_Y ×_{FÉt_Z} FÉt_X`.
* `AlgebraicGeometry.finiteEtalePushoutGluingIso` — the canonical identification of the two ways
  of restricting a finite étale cover of `Y ⨿_Z X` to `Z`.
* `AlgebraicGeometry.finiteEtalePushoutRestriction` — the restriction functor from the finite
  étale covers of `Y ⨿_Z X` to the 2-fibre product `FÉt_Y ×_{FÉt_Z} FÉt_X`.
* `AlgebraicGeometry.finiteEtalePushoutEquivalence` — that restriction functor, read as an
  equivalence of categories.

## Main results

* `AlgebraicGeometry.finiteEtale_pushoutMap` — the morphism of pushouts attached to a finite
  étale cartesian triple is finite étale.
* `AlgebraicGeometry.finiteEtaleTripleToOver_full`,
  `AlgebraicGeometry.finiteEtaleTripleToOver_faithful` and
  `AlgebraicGeometry.finiteEtaleTripleToOver_essSurj` — the pushout of a finite étale triple is
  an equivalence onto the finite étale covers of `Y ⨿_Z X`.
* `AlgebraicGeometry.finiteEtaleTripleToOverCompRestrictionIso` — restricting the pushout of a
  finite étale triple back to `Y` and to `X` recovers the triple.
* `AlgebraicGeometry.finiteEtalePushoutRestriction_isEquivalence` — the restriction functor of
  [Stacks Project, Tag 0EK4] is an equivalence of categories.

## References

* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
* [Stacks Project, Tag 0EK4](https://stacks.math.columbia.edu/tag/0EK4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism of pushouts attached to a cartesian diagram with finite étale morphisms over
`X` and over `Y` is itself finite étale.  Étaleness is [Stacks Project, Tag 0ECL]; finiteness
holds because the morphism is separated, locally of finite type and locally quasi-finite by
[Stacks Project, Tag 0ECK], and universally closed because its restrictions along the two
canonical morphisms into the upper pushout are a finite morphism followed by an integral one and
those two morphisms are jointly surjective. -/
theorem finiteEtale_pushoutMap (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (d : CartesianDiagram s) (hf : finiteEtale d.f) (hg : finiteEtale d.g) :
    finiteEtale (pushoutMap s d) := by
  have : IsFinite d.f := hf.1
  have : IsFinite d.g := hg.1
  have : Etale d.f := hf.2
  have : Etale d.g := hg.2
  have : IsFinite d.h := MorphismProperty.of_isPullback d.left_isPullback hf.1
  have : Etale d.h := MorphismProperty.of_isPullback d.left_isPullback hf.2
  refine ⟨?_, etale_pushoutMap s d⟩
  have : UniversallyClosed (pushoutInl (inducedSituation s d) ≫ pushoutMap s d) := by
    rw [pushoutMap, IsPushout.inl_desc]
    infer_instance
  have : UniversallyClosed (pushoutInr (inducedSituation s d) ≫ pushoutMap s d) := by
    rw [pushoutMap, IsPushout.inr_desc]
    infer_instance
  have : UniversallyClosed (pushoutMap s d) :=
    universallyClosed_of_jointly_surjective _ _ (pushoutMap s d)
      (pushoutInl_inr_jointly_surjective (inducedSituation s d))
  have : IsProper (pushoutMap s d) := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite (pushoutMap s d)

/-- The cartesian diagrams over a pushout situation whose three vertical morphisms are finite
étale.  Together with `AlgebraicGeometry.CartesianTripleHom` these are one side of the
comparison of [Stacks Project, Tag 0EK4]. -/
abbrev FiniteEtaleCartesianTriple (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :=
  {d : CartesianDiagram s // finiteEtale d.f ∧ finiteEtale d.g ∧ finiteEtale d.h}

/-- The category of finite étale cartesian triples over `s`, whose morphisms are the morphisms
of the underlying cartesian diagrams. -/
instance (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    Category (FiniteEtaleCartesianTriple s) where
  Hom d e := CartesianTripleHom d.1 e.1
  id d := CartesianTripleHom.id d.1
  comp a b := CartesianTripleHom.comp a b
  id_comp a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  comp_id a := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, CartesianTripleHom.id]
  assoc a b c := by
    apply CartesianTripleHom.ext <;> simp [CartesianTripleHom.comp, Category.assoc]

/-- The pushout of a finite étale cartesian triple, as a finite étale cover of `Y ⨿_Z X`.  On
morphisms it is the morphism of pushouts induced by the three components. -/
noncomputable def finiteEtaleTripleToOver
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FiniteEtaleCartesianTriple s ⥤ FiniteEtaleOver (pushoutScheme s) where
  obj d := MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (pushoutMap s d.1)
    (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1)
  map {d e} m := MorphismProperty.Over.homMk (triplePushoutMap m)
    (triplePushoutMap_comp_pushoutMap m)
  map_id d := by ext; exact triplePushoutMap_id d.1
  map_comp m n := by ext; exact triplePushoutMap_comp m n

/-- The cover `Z' ⟶ Z` of a cartesian triple is canonically the base change along `j` of its
cover `Y' ⟶ Y`, because the right-hand square of the triple is cartesian. -/
noncomputable def finiteEtaleTripleIsoRight
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    (d : CartesianDiagram s) (hg : finiteEtale d.g) (hh : finiteEtale d.h) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.h hh) ≅
      (finiteEtaleBaseChange s.j).obj
        (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.g hg) :=
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget d.Y').mapIso d.right_isPullback.isoOverPullback)
    d.right_isPullback.isoOverPullback_hom_left_comp_snd

/-- The cover `Z' ⟶ Z` of a cartesian triple is canonically the base change along `i` of its
cover `X' ⟶ X`, because the left-hand square of the triple is cartesian. -/
noncomputable def finiteEtaleTripleIsoLeft
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    (d : CartesianDiagram s) (hf : finiteEtale d.f) (hh : finiteEtale d.h) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.h hh) ≅
      (finiteEtaleBaseChange s.i).obj
        (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.f hf) :=
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget d.X').mapIso d.left_isPullback.isoOverPullback)
    d.left_isPullback.isoOverPullback_hom_left_comp_snd

/-- The identification of `Z'` with the base change of `Y'` along `j` is compatible with the
morphism `j' : Z' ⟶ Y'` of the triple. -/
theorem finiteEtaleTripleIsoRight_hom_left_fst
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    (d : CartesianDiagram s) (hg : finiteEtale d.g) (hh : finiteEtale d.h) :
    (finiteEtaleTripleIsoRight d hg hh).hom.left ≫ pullback.fst d.g s.j = d.j' :=
  CategoryTheory.Over.w d.right_isPullback.isoOverPullback.hom

/-- The identification of `Z'` with the base change of `X'` along `i` is compatible with the
morphism `i' : Z' ⟶ X'` of the triple. -/
theorem finiteEtaleTripleIsoLeft_hom_left_fst
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    (d : CartesianDiagram s) (hf : finiteEtale d.f) (hh : finiteEtale d.h) :
    (finiteEtaleTripleIsoLeft d hf hh).hom.left ≫ pullback.fst d.f s.i = d.i' :=
  CategoryTheory.Over.w d.left_isPullback.isoOverPullback.hom

/-- A morphism into a base change of finite étale covers is determined by its first
projection: the second projection is the structure morphism on both sides. -/
theorem finiteEtaleBaseChange_hom_ext {X Y : Scheme.{u}} (g : X ⟶ Y) {B : FiniteEtaleOver Y}
    {P : FiniteEtaleOver X} {u v : P ⟶ (finiteEtaleBaseChange g).obj B}
    (h : u.left ≫ pullback.fst B.hom g = v.left ≫ pullback.fst B.hom g) : u = v :=
  MorphismProperty.Over.Hom.ext
    (pullback.hom_ext h
      ((MorphismProperty.Over.w u).trans (MorphismProperty.Over.w v).symm))

/-- The first projection of a morphism followed by a base-changed morphism. -/
theorem comp_finiteEtaleBaseChange_map_left_fst {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : FiniteEtaleOver Y} {P : FiniteEtaleOver X}
    (α : P ⟶ (finiteEtaleBaseChange g).obj A) (φ : A ⟶ B) :
    (α ≫ (finiteEtaleBaseChange g).map φ).left ≫ pullback.fst B.hom g
      = α.left ≫ pullback.fst A.hom g ≫ φ.left :=
  (congrArg (· ≫ pullback.fst B.hom g) (MorphismProperty.Comma.comp_left α _)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (α.left ≫ ·) (finiteEtaleBaseChange_map_left_fst g φ)))

/-- The first projection of a composite of morphisms of finite étale covers. -/
theorem comp_left_comp_fst {X Y : Scheme.{u}} (g : X ⟶ Y) {B : FiniteEtaleOver Y}
    {P Q : FiniteEtaleOver X} (u : P ⟶ Q) (v : Q ⟶ (finiteEtaleBaseChange g).obj B) :
    (u ≫ v).left ≫ pullback.fst B.hom g = u.left ≫ v.left ≫ pullback.fst B.hom g :=
  (congrArg (· ≫ pullback.fst B.hom g) (MorphismProperty.Comma.comp_left u v)).trans
    (Category.assoc _ _ _)

/-- A square of morphisms of finite étale covers over a base change commutes if and only if it
does after composing with the first projections. -/
private theorem comp_baseChange_map_eq_iff {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : FiniteEtaleOver Y} {P Q : FiniteEtaleOver X} (α : P ⟶ (finiteEtaleBaseChange g).obj A)
    (β : Q ⟶ (finiteEtaleBaseChange g).obj B) (φ : A ⟶ B) (ψ : P ⟶ Q) :
    α ≫ (finiteEtaleBaseChange g).map φ = ψ ≫ β ↔
      α.left ≫ pullback.fst A.hom g ≫ φ.left = ψ.left ≫ β.left ≫ pullback.fst B.hom g :=
  ⟨fun h ↦ (comp_finiteEtaleBaseChange_map_left_fst g α φ).symm.trans
      ((congrArg (fun q ↦ q.left ≫ pullback.fst B.hom g) h).trans (comp_left_comp_fst g ψ β)),
    fun h ↦ finiteEtaleBaseChange_hom_ext g
      ((comp_finiteEtaleBaseChange_map_left_fst g α φ).trans
        (h.trans (comp_left_comp_fst g ψ β).symm))⟩

/-- A morphism of finite étale cartesian triples, read on the covers of `Y`. -/
noncomputable def tripleHomY {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.g d.2.2.1 :
        FiniteEtaleOver s.Y) ⟶
      MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) e.1.g e.2.2.1 :=
  MorphismProperty.Over.homMk m.y m.overY

/-- A morphism of finite étale cartesian triples, read on the covers of `X`. -/
noncomputable def tripleHomX {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.f d.2.1 :
        FiniteEtaleOver s.X) ⟶
      MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) e.1.f e.2.1 :=
  MorphismProperty.Over.homMk m.x m.overX

/-- A morphism of finite étale cartesian triples, read on the covers of `Z`. -/
noncomputable def tripleHomZ {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.h d.2.2.2 :
        FiniteEtaleOver s.Z) ⟶
      MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) e.1.h e.2.2.2 :=
  MorphismProperty.Over.homMk m.z m.overZ

/-- The identification of `Z'` with the base change of `Y'` along `j` is natural in the
cartesian triple. -/
theorem tripleIsoRight_naturality
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫
        (finiteEtaleBaseChange s.j).map (tripleHomY m) =
      tripleHomZ m ≫ (finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2).hom :=
  (comp_baseChange_map_eq_iff s.j _ _ _ _).2 <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ m.y) (finiteEtaleTripleIsoRight_hom_left_fst d.1 d.2.2.1 d.2.2.2)).trans <|
        m.right.trans
          (congrArg (m.z ≫ ·) (finiteEtaleTripleIsoRight_hom_left_fst e.1 e.2.2.1 e.2.2.2).symm)

/-- The identification of `Z'` with the base change of `X'` along `i` is natural in the
cartesian triple. -/
theorem tripleIsoLeft_naturality
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (finiteEtaleTripleIsoLeft d.1 d.2.1 d.2.2.2).hom ≫
        (finiteEtaleBaseChange s.i).map (tripleHomX m) =
      tripleHomZ m ≫ (finiteEtaleTripleIsoLeft e.1 e.2.1 e.2.2.2).hom :=
  (comp_baseChange_map_eq_iff s.i _ _ _ _).2 <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ m.x) (finiteEtaleTripleIsoLeft_hom_left_fst d.1 d.2.1 d.2.2.2)).trans <|
        m.left.trans
          (congrArg (m.z ≫ ·) (finiteEtaleTripleIsoLeft_hom_left_fst e.1 e.2.1 e.2.2.2).symm)

/-- A finite étale cartesian triple, read as an object of the 2-fibre product
`FÉt_Y ×_{FÉt_Z} FÉt_X`: its covers of `Y` and of `X`, together with the identification of their
restrictions to `Z` furnished by the two cartesian squares. -/
noncomputable def finiteEtaleTripleToCategoricalPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FiniteEtaleCartesianTriple s ⥤
      CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i) where
  obj d := ⟨MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.g d.2.2.1,
    MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.f d.2.1,
    (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).symm ≪≫
      finiteEtaleTripleIsoLeft d.1 d.2.1 d.2.2.2⟩
  map {d e} m :=
    { fst := tripleHomY m
      snd := tripleHomX m
      w := (cancel_epi (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom).1
        (((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ ((finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2).inv ≫
              (finiteEtaleTripleIsoLeft e.1 e.2.1 e.2.2.2).hom))
              (tripleIsoRight_naturality m))).trans
          (((Category.assoc _ _ _).trans
              (congrArg (tripleHomZ m ≫ ·)
                (Iso.hom_inv_id_assoc (finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2) _))).trans
            ((tripleIsoLeft_naturality m).symm.trans
              ((Iso.hom_inv_id_assoc (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2) _).symm.trans
                (congrArg ((finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫ ·)
                  (Category.assoc _ _ _).symm))))) }
  map_id _ := CategoricalPullback.hom_ext
    (MorphismProperty.Over.Hom.ext rfl) (MorphismProperty.Over.Hom.ext rfl)
  map_comp _ _ := CategoricalPullback.hom_ext
    (MorphismProperty.Over.Hom.ext rfl) (MorphismProperty.Over.Hom.ext rfl)

/-- The pushout of finite étale triples is faithful: a morphism of cartesian diagrams is
determined by the morphism of pushouts it induces. -/
instance finiteEtaleTripleToOver_faithful
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToOver s).Faithful where
  map_injective h := triplePushoutMap_injective (congrArg (fun q ↦ q.left) h)

/-- The pushout of finite étale triples is full: every morphism of pushouts lying over
`Y ⨿_Z X` comes from a morphism of cartesian diagrams. -/
instance finiteEtaleTripleToOver_full
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToOver s).Full where
  map_surjective {d e} f := by
    obtain ⟨m, hm⟩ := exists_cartesianTripleHom_of_comp_pushoutMap d.1 e.1 f.left
      (MorphismProperty.Over.w f)
    exact ⟨m, MorphismProperty.Over.Hom.ext hm⟩

/-- The pushout of finite étale triples is essentially surjective: a finite étale cover of
`Y ⨿_Z X` is the pushout of its two base changes, by [Stacks Project, Tag 0ECL]. -/
instance finiteEtaleTripleToOver_essSurj
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToOver s).EssSurj where
  mem_essImage U := by
    have hfin : IsFinite U.hom := U.prop.1
    have hEt : Etale U.hom := U.prop.2
    let W : Over (pushoutScheme s) :=
      (MorphismProperty.Over.forget finiteEtale ⊤ (pushoutScheme s)).obj U
    have hw : Flat U.hom ∧ IsSeparated U.hom ∧
        LocallyOfFiniteType U.hom ∧ LocallyQuasiFinite U.hom :=
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    have hdf : finiteEtale (pushoutBaseChangeDiagram s W hw).f := by
      dsimp [pushoutBaseChangeDiagram]
      exact MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback W.hom (pushoutInl s)) U.prop
    have hdg : finiteEtale (pushoutBaseChangeDiagram s W hw).g := by
      dsimp [pushoutBaseChangeDiagram]
      exact MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback W.hom (pushoutInr s)) U.prop
    have hdh : finiteEtale (pushoutBaseChangeDiagram s W hw).h :=
      MorphismProperty.of_isPullback (pushoutBaseChangeDiagram s W hw).left_isPullback hdf
    obtain ⟨cinv, hc₁, hc₂⟩ := (isIso_pushoutBaseChangeMap s W hw).out
    exact ⟨⟨pushoutBaseChangeDiagram s W hw, hdf, hdg, hdh⟩,
      ⟨MorphismProperty.Over.isoMk ⟨pushoutBaseChangeMap s W hw, cinv, hc₁, hc₂⟩
        (pushoutBaseChangeMap_comp_hom s W hw)⟩⟩

/-- The canonical identification of the two ways of restricting a finite étale cover of the
pushout `Y ⨿_Z X` to `Z`: along `Y` and then `j`, or along `X` and then `i`.  It is the
composition of the two base-change comparisons with the commutativity of the pushout square. -/
noncomputable def finiteEtalePushoutGluingIso
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    finiteEtaleBaseChange (pushoutInr s) ⋙ finiteEtaleBaseChange s.j ≅
      finiteEtaleBaseChange (pushoutInl s) ⋙ finiteEtaleBaseChange s.i :=
  (MorphismProperty.Over.pullbackComp
      (P := finiteEtale) (Q := ⊤) s.j (pushoutInr s)).symm ≪≫
    MorphismProperty.Over.pullbackCongr (P := finiteEtale) (Q := ⊤)
      (show s.j ≫ pushoutInr s = s.i ≫ pushoutInl s from
        (pushoutAlongClosedImmersionAndIntegral s).isPushout.w.symm) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := finiteEtale) (Q := ⊤) s.i (pushoutInl s)

/-- The restriction functor of [Stacks Project, Tag 0EK4]: a finite étale cover of `Y ⨿_Z X` is
sent to its base changes to `Y` and to `X` together with the canonical identification of their
restrictions to `Z`, that is to an object of `FÉt_Y ×_{FÉt_Z} FÉt_X`. -/
noncomputable def finiteEtalePushoutRestriction
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FiniteEtaleOver (pushoutScheme s) ⥤
      CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i) where
  obj U := ⟨(finiteEtaleBaseChange (pushoutInr s)).obj U,
    (finiteEtaleBaseChange (pushoutInl s)).obj U, (finiteEtalePushoutGluingIso s).app U⟩
  map f := ⟨(finiteEtaleBaseChange (pushoutInr s)).map f,
    (finiteEtaleBaseChange (pushoutInl s)).map f,
    (finiteEtalePushoutGluingIso s).hom.naturality f⟩
  map_id U := CategoricalPullback.hom_ext
    ((finiteEtaleBaseChange (pushoutInr s)).map_id U)
    ((finiteEtaleBaseChange (pushoutInl s)).map_id U)
  map_comp f g := CategoricalPullback.hom_ext
    ((finiteEtaleBaseChange (pushoutInr s)).map_comp f g)
    ((finiteEtaleBaseChange (pushoutInl s)).map_comp f g)

/-- Reading a finite étale triple in the 2-fibre product is faithful: the components over `X`
and over `Y` are recorded, and the component over `Z` is determined by them because the
left-hand square of the target triple is cartesian. -/
instance finiteEtaleTripleToCategoricalPullback_faithful
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToCategoricalPullback s).Faithful where
  map_injective {d e} {m n} h := by
    have hy : m.y = n.y := congrArg (fun q ↦ q.left) (congrArg (fun q ↦ q.fst) h)
    have hx : m.x = n.x := congrArg (fun q ↦ q.left) (congrArg (fun q ↦ q.snd) h)
    refine CartesianTripleHom.ext hx hy ?_
    refine e.1.left_isPullback.hom_ext ?_ ?_
    · rw [← m.left, ← n.left, hx]
    · rw [m.overZ, n.overZ]

section Comparison

attribute [local implicit_reducible] finiteEtaleBaseChange
attribute [local implicit_reducible] MorphismProperty.Over.pullback MorphismProperty.Over.mk

/-- Transposing a commuting square of isomorphisms: if `u` followed by `β` agrees with `α`
followed by `v`, then `α⁻¹` followed by `u` agrees with `v` followed by `β⁻¹`. -/
theorem inv_comp_eq_comp_inv {C : Type*} [Category C] {A A' B B' : C} (α : A ≅ A') (β : B ≅ B')
    {u : A ⟶ B} {v : A' ⟶ B'} (h : u ≫ β.hom = α.hom ≫ v) : α.inv ≫ u = v ≫ β.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transposing a commuting square of isomorphisms, in the other direction. -/
theorem comp_inv_eq_inv_comp {C : Type*} [Category C] {A A' B B' : C} (α : A ≅ A') (β : B ≅ B')
    {u : A' ⟶ B'} {v : A ⟶ B} (h : α.hom ≫ u = v ≫ β.hom) : u ≫ β.inv = α.inv ≫ v := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, h]

/-- The underlying morphism of schemes of the inverse of an isomorphism of finite étale covers is
inverse to that of the isomorphism. -/
theorem finiteEtaleOver_iso_inv_left_comp_hom_left {X : Scheme.{u}} {A B : FiniteEtaleOver X}
    (e : A ≅ B) : e.inv.left ≫ e.hom.left = 𝟙 B.left :=
  congrArg (fun q : B ⟶ B ↦ q.left) (Iso.inv_hom_id e)

/-- A morphism into a base change of finite étale covers, followed by the first projection and
then the structure morphism of the cover, is the structure morphism followed by the base-change
morphism. -/
theorem finiteEtaleBaseChange_hom_left_fst_comp {X Y : Scheme.{u}} (g : X ⟶ Y)
    {B : FiniteEtaleOver Y} {P : FiniteEtaleOver X} (u : P ⟶ (finiteEtaleBaseChange g).obj B) :
    u.left ≫ pullback.fst B.hom g ≫ B.hom = P.hom ≫ g :=
  (congrArg (u.left ≫ ·) pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) (MorphismProperty.Over.w u)))

/-- A morphism into an iterated base change of finite étale covers is determined by its
projection to the cover one started from: the remaining components are structure morphisms. -/
theorem finiteEtaleBaseChange_hom_ext_fst {X Y V : Scheme.{u}} (g : X ⟶ Y) (b : Y ⟶ V)
    {W : FiniteEtaleOver V} {P : FiniteEtaleOver X}
    {u v : P ⟶ (finiteEtaleBaseChange g).obj ((finiteEtaleBaseChange b).obj W)}
    (h : u.left ≫ pullback.fst (pullback.snd W.hom b) g ≫ pullback.fst W.hom b
      = v.left ≫ pullback.fst (pullback.snd W.hom b) g ≫ pullback.fst W.hom b) : u = v := by
  refine finiteEtaleBaseChange_hom_ext g (pullback.hom_ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  · exact (finiteEtaleBaseChange_hom_left_fst_comp g u).trans
      (finiteEtaleBaseChange_hom_left_fst_comp g v).symm

/-- The projection to the original cover of an iterated base change of a morphism of finite étale
covers. -/
theorem finiteEtaleBaseChange_map_left_fst_fst {S X Z : Scheme.{u}} (b : X ⟶ S) (c : Z ⟶ X)
    {A : FiniteEtaleOver X} {W : FiniteEtaleOver S}
    (e : A ⟶ (finiteEtaleBaseChange b).obj W) :
    ((finiteEtaleBaseChange c).map e).left ≫
        pullback.fst (pullback.snd W.hom b) c ≫ pullback.fst W.hom b =
      pullback.fst A.hom c ≫ e.left ≫ pullback.fst W.hom b :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst W.hom b) (finiteEtaleBaseChange_map_left_fst c e)).trans
      (Category.assoc _ _ _))

/-- Reading the identification of `Z'` with the base change of `Y'` along `j` backwards: the
inverse followed by `j' : Z' ⟶ Y'` is the first projection of the base change. -/
theorem finiteEtaleTripleIsoRight_inv_left_comp_j'
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hg : finiteEtale d.g) (hh : finiteEtale d.h) :
    (finiteEtaleTripleIsoRight d hg hh).inv.left ≫ d.j' = pullback.fst d.g s.j :=
  (congrArg ((finiteEtaleTripleIsoRight d hg hh).inv.left ≫ ·)
      (finiteEtaleTripleIsoRight_hom_left_fst d hg hh).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst d.g s.j)
          (finiteEtaleOver_iso_inv_left_comp_hom_left
            (finiteEtaleTripleIsoRight d hg hh))).trans (Category.id_comp _)))

/-- The gluing identification of [Stacks Project, Tag 0EK4] is compatible with the projections to
the finite étale cover of `Y ⨿_Z X` one started from: restricting first to `Y` and then to `Z`
projects to the same morphism as restricting first to `X` and then to `Z`. -/
theorem finiteEtalePushoutGluingIso_hom_left_fst_fst
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (W : FiniteEtaleOver (pushoutScheme s)) :
    ((finiteEtalePushoutGluingIso s).app W).hom.left ≫
        pullback.fst (pullback.snd W.hom (pushoutInl s)) s.i ≫
          pullback.fst W.hom (pushoutInl s) =
      pullback.fst (pullback.snd W.hom (pushoutInr s)) s.j ≫
        pullback.fst W.hom (pushoutInr s) := by
  have hw : s.j ≫ pushoutInr s = s.i ≫ pushoutInl s :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.w.symm
  set e := MorphismProperty.Over.pullbackComp (P := finiteEtale) (Q := ⊤) s.j (pushoutInr s)
    with he
  have hdec : ((finiteEtalePushoutGluingIso s).app W).hom =
      e.inv.app W ≫
        (MorphismProperty.Over.pullbackCongr (P := finiteEtale) (Q := ⊤) hw).hom.app W ≫
        (MorphismProperty.Over.pullbackComp (P := finiteEtale) (Q := ⊤) s.i
          (pushoutInl s)).hom.app W := rfl
  have hinv : (e.inv.app W).left ≫ (e.hom.app W).left = 𝟙 _ := by
    rw [← MorphismProperty.Comma.comp_left, Iso.inv_hom_id_app]
    rfl
  have h2 : (e.inv.app W).left ≫ pullback.fst W.hom (s.j ≫ pushoutInr s) =
      pullback.fst (pullback.snd W.hom (pushoutInr s)) s.j ≫
        pullback.fst W.hom (pushoutInr s) :=
    calc (e.inv.app W).left ≫ pullback.fst W.hom (s.j ≫ pushoutInr s)
        = (e.inv.app W).left ≫ (e.hom.app W).left ≫
            (pullback.fst (pullback.snd W.hom (pushoutInr s)) s.j ≫
              pullback.fst W.hom (pushoutInr s)) := by
          rw [he, MorphismProperty.Over.pullbackComp_left_fst_fst s.j (pushoutInr s) W]
      _ = ((e.inv.app W).left ≫ (e.hom.app W).left) ≫
            (pullback.fst (pullback.snd W.hom (pushoutInr s)) s.j ≫
              pullback.fst W.hom (pushoutInr s)) := (Category.assoc _ _ _).symm
      _ = _ := by rw [hinv, Category.id_comp]
  rw [hdec, MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
    Category.assoc, Category.assoc,
    MorphismProperty.Over.pullbackComp_left_fst_fst s.i (pushoutInl s) W,
    MorphismProperty.Over.pullbackCongr_hom_app_left_fst hw W, h2]

/-- The cover `Y' ⟶ Y` of a cartesian triple is canonically the restriction to `Y` of the finite
étale cover `Y' ⨿_{Z'} X' ⟶ Y ⨿_Z X`, because that square is cartesian by
[Stacks Project, Tag 0ECK]. -/
noncomputable def pushoutRestrictionIsoRight
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hp : finiteEtale (pushoutMap s d)) (hg : finiteEtale d.g) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.g hg : FiniteEtaleOver s.Y) ≅
      (finiteEtaleBaseChange (pushoutInr s)).obj
        (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (pushoutMap s d) hp) :=
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget _).mapIso (pushoutMap_right_isPullback s d).isoOverPullback)
    (pushoutMap_right_isPullback s d).isoOverPullback_hom_left_comp_snd

/-- The identification of `Y'` with the restriction to `Y` of the upper pushout is compatible
with the canonical morphism `Y' ⟶ Y' ⨿_{Z'} X'`. -/
theorem pushoutRestrictionIsoRight_hom_left_fst
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hp : finiteEtale (pushoutMap s d)) (hg : finiteEtale d.g) :
    (pushoutRestrictionIsoRight d hp hg).hom.left ≫ pullback.fst (pushoutMap s d) (pushoutInr s)
      = pushoutInr (inducedSituation s d) :=
  CategoryTheory.Over.w (pushoutMap_right_isPullback s d).isoOverPullback.hom

/-- The cover `X' ⟶ X` of a cartesian triple is canonically the restriction to `X` of the finite
étale cover `Y' ⨿_{Z'} X' ⟶ Y ⨿_Z X`, because that square is cartesian by
[Stacks Project, Tag 0ECK]. -/
noncomputable def pushoutRestrictionIsoLeft
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hp : finiteEtale (pushoutMap s d)) (hf : finiteEtale d.f) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.f hf : FiniteEtaleOver s.X) ≅
      (finiteEtaleBaseChange (pushoutInl s)).obj
        (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (pushoutMap s d) hp) :=
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget _).mapIso (pushoutMap_left_isPullback s d).isoOverPullback)
    (pushoutMap_left_isPullback s d).isoOverPullback_hom_left_comp_snd

/-- The identification of `X'` with the restriction to `X` of the upper pushout is compatible
with the canonical morphism `X' ⟶ Y' ⨿_{Z'} X'`. -/
theorem pushoutRestrictionIsoLeft_hom_left_fst
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hp : finiteEtale (pushoutMap s d)) (hf : finiteEtale d.f) :
    (pushoutRestrictionIsoLeft d hp hf).hom.left ≫ pullback.fst (pushoutMap s d) (pushoutInl s)
      = pushoutInl (inducedSituation s d) :=
  CategoryTheory.Over.w (pushoutMap_left_isPullback s d).isoOverPullback.hom

/-- The projection to `Y' ⨿_{Z'} X'` of the two identifications of the restriction to `Z` of the
pushout of a cartesian triple.  Both are the canonical morphism of the upper pushout square, so
the two agree precisely because that square commutes. -/
theorem pushoutRestrictionIso_compatibility_core
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hf : finiteEtale d.f) (hg : finiteEtale d.g) (hh : finiteEtale d.h)
    (hp : finiteEtale (pushoutMap s d)) :
    ((finiteEtaleTripleIsoRight d hg hh).symm ≪≫ finiteEtaleTripleIsoLeft d hf hh).hom.left ≫
        pullback.fst d.f s.i ≫ (pushoutRestrictionIsoLeft d hp hf).hom.left ≫
          pullback.fst (pushoutMap s d) (pushoutInl s) =
      pullback.fst d.g s.j ≫ (pushoutRestrictionIsoRight d hp hg).hom.left ≫
        pullback.fst (pushoutMap s d) (pushoutInr s) := by
  rw [pushoutRestrictionIsoLeft_hom_left_fst d hp hf,
    pushoutRestrictionIsoRight_hom_left_fst d hp hg, Iso.trans_hom, Iso.symm_hom,
    MorphismProperty.Comma.comp_left, Category.assoc, ← Category.assoc _ _
      (pushoutInl (inducedSituation s d)),
    finiteEtaleTripleIsoLeft_hom_left_fst d hf hh,
    (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout.w,
    ← Category.assoc, finiteEtaleTripleIsoRight_inv_left_comp_j' d hg hh]

/-- The gluing identification of a cartesian triple and the gluing identification of its pushout
agree under the two restriction isomorphisms.  This is the compatibility making the comparison of
[Stacks Project, Tag 0EK4] a morphism of the 2-fibre product. -/
theorem pushoutRestrictionIso_compatibility
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}} (d : CartesianDiagram s)
    (hf : finiteEtale d.f) (hg : finiteEtale d.g) (hh : finiteEtale d.h) :
    ((finiteEtaleTripleIsoRight d hg hh).symm ≪≫ finiteEtaleTripleIsoLeft d hf hh).hom ≫
        (finiteEtaleBaseChange s.i).map
          (pushoutRestrictionIsoLeft d (finiteEtale_pushoutMap s d hf hg) hf).hom =
      (finiteEtaleBaseChange s.j).map
          (pushoutRestrictionIsoRight d (finiteEtale_pushoutMap s d hf hg) hg).hom ≫
        ((finiteEtalePushoutGluingIso s).app
          (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (pushoutMap s d)
            (finiteEtale_pushoutMap s d hf hg))).hom := by
  refine finiteEtaleBaseChange_hom_ext_fst s.i (pushoutInl s) ?_
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
    Category.assoc, Category.assoc, finiteEtalePushoutGluingIso_hom_left_fst_fst s,
    finiteEtaleBaseChange_map_left_fst_fst (pushoutInl s) s.i
      (pushoutRestrictionIsoLeft d (finiteEtale_pushoutMap s d hf hg) hf).hom,
    finiteEtaleBaseChange_map_left_fst_fst (pushoutInr s) s.j
      (pushoutRestrictionIsoRight d (finiteEtale_pushoutMap s d hf hg) hg).hom]
  exact pushoutRestrictionIso_compatibility_core d hf hg hh (finiteEtale_pushoutMap s d hf hg)

/-- The identification of `Y'` with the restriction to `Y` of the upper pushout is natural in the
cartesian triple. -/
theorem pushoutRestrictionIsoRight_naturality
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (pushoutRestrictionIsoRight d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.2.1).hom ≫
        (finiteEtaleBaseChange (pushoutInr s)).map ((finiteEtaleTripleToOver s).map m) =
      tripleHomY m ≫
        (pushoutRestrictionIsoRight e.1 (finiteEtale_pushoutMap s e.1 e.2.1 e.2.2.1)
          e.2.2.1).hom :=
  (comp_baseChange_map_eq_iff (pushoutInr s) _ _ _ _).2 <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ triplePushoutMap m)
          (pushoutRestrictionIsoRight_hom_left_fst d.1
            (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.2.1)).trans <|
        (pushoutInr_comp_triplePushoutMap m).trans
          (congrArg (m.y ≫ ·)
            (pushoutRestrictionIsoRight_hom_left_fst e.1
              (finiteEtale_pushoutMap s e.1 e.2.1 e.2.2.1) e.2.2.1).symm)

/-- The identification of `X'` with the restriction to `X` of the upper pushout is natural in the
cartesian triple. -/
theorem pushoutRestrictionIsoLeft_naturality
    {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}
    {d e : FiniteEtaleCartesianTriple s} (m : d ⟶ e) :
    (pushoutRestrictionIsoLeft d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.1).hom ≫
        (finiteEtaleBaseChange (pushoutInl s)).map ((finiteEtaleTripleToOver s).map m) =
      tripleHomX m ≫
        (pushoutRestrictionIsoLeft e.1 (finiteEtale_pushoutMap s e.1 e.2.1 e.2.2.1)
          e.2.1).hom :=
  (comp_baseChange_map_eq_iff (pushoutInl s) _ _ _ _).2 <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ triplePushoutMap m)
          (pushoutRestrictionIsoLeft_hom_left_fst d.1
            (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.1)).trans <|
        (pushoutInl_comp_triplePushoutMap m).trans
          (congrArg (m.x ≫ ·)
            (pushoutRestrictionIsoLeft_hom_left_fst e.1
              (finiteEtale_pushoutMap s e.1 e.2.1 e.2.2.1) e.2.1).symm)

/-- Reading a finite étale cartesian triple in the 2-fibre product `FÉt_Y ×_{FÉt_Z} FÉt_X` is
the same as taking its pushout and then restricting that finite étale cover of `Y ⨿_Z X` back to
`Y` and to `X`: the two squares of [Stacks Project, Tag 0ECK] identify the restrictions of the
pushout with the covers one started from. -/
noncomputable def finiteEtaleTripleToOverCompRestrictionIso
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    finiteEtaleTripleToOver s ⋙ finiteEtalePushoutRestriction s ≅
      finiteEtaleTripleToCategoricalPullback s :=
  NatIso.ofComponents
    (fun d ↦ CategoricalPullback.mkIso
      (pushoutRestrictionIsoRight d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.2.1).symm
      (pushoutRestrictionIsoLeft d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.1).symm
      (inv_comp_eq_comp_inv
        ((finiteEtaleBaseChange s.j).mapIso
          (pushoutRestrictionIsoRight d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.2.1))
        ((finiteEtaleBaseChange s.i).mapIso
          (pushoutRestrictionIsoLeft d.1 (finiteEtale_pushoutMap s d.1 d.2.1 d.2.2.1) d.2.1))
        (pushoutRestrictionIso_compatibility d.1 d.2.1 d.2.2.1 d.2.2.2)))
    (fun m ↦ CategoricalPullback.hom_ext
      (comp_inv_eq_inv_comp _ _ (pushoutRestrictionIsoRight_naturality m))
      (comp_inv_eq_inv_comp _ _ (pushoutRestrictionIsoLeft_naturality m)))

end Comparison

section Equivalence

variable {s : PushoutAlongClosedImmersionAndIntegralSituation.{u}}

/-- The component over `Z` of the morphism of cartesian triples underlying a morphism of the
2-fibre product: transport the component over `Y` through the two cartesian squares on the
integral side. -/
noncomputable def categoricalPullbackHomZ {d e : FiniteEtaleCartesianTriple s}
    (φ : (finiteEtaleTripleToCategoricalPullback s).obj d ⟶
      (finiteEtaleTripleToCategoricalPullback s).obj e) :
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) d.1.h d.2.2.2 :
        FiniteEtaleOver s.Z) ⟶
      MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) e.1.h e.2.2.2 :=
  (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫
    (finiteEtaleBaseChange s.j).map φ.fst ≫
      (finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2).inv

/-- By construction the component over `Z` is compatible with the identifications of the covers
of `Z` with the base changes of the covers of `Y`. -/
theorem categoricalPullbackHomZ_comp_isoRight {d e : FiniteEtaleCartesianTriple s}
    (φ : (finiteEtaleTripleToCategoricalPullback s).obj d ⟶
      (finiteEtaleTripleToCategoricalPullback s).obj e) :
    categoricalPullbackHomZ φ ≫ (finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2).hom =
      (finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫
        (finiteEtaleBaseChange s.j).map φ.fst :=
  (Category.assoc _ _ _).trans
    (congrArg ((finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫ ·)
      ((Category.assoc _ _ _).trans
        ((congrArg ((finiteEtaleBaseChange s.j).map φ.fst ≫ ·)
            (Iso.inv_hom_id (finiteEtaleTripleIsoRight e.1 e.2.2.1 e.2.2.2))).trans
          (Category.comp_id _))))

/-- The component over `Z` is also compatible with the identifications of the covers of `Z` with
the base changes of the covers of `X`; this is exactly the compatibility carried by a morphism of
the 2-fibre product. -/
theorem categoricalPullbackHomZ_comp_isoLeft {d e : FiniteEtaleCartesianTriple s}
    (φ : (finiteEtaleTripleToCategoricalPullback s).obj d ⟶
      (finiteEtaleTripleToCategoricalPullback s).obj e) :
    categoricalPullbackHomZ φ ≫ (finiteEtaleTripleIsoLeft e.1 e.2.1 e.2.2.2).hom =
      (finiteEtaleTripleIsoLeft d.1 d.2.1 d.2.2.2).hom ≫
        (finiteEtaleBaseChange s.i).map φ.snd :=
  (Category.assoc _ _ _).trans
    ((congrArg ((finiteEtaleTripleIsoRight d.1 d.2.2.1 d.2.2.2).hom ≫ ·)
        ((Category.assoc _ _ _).trans (φ.w.trans (Category.assoc _ _ _)))).trans
      (Iso.hom_inv_id_assoc _ _))

/-- The component over `Z` commutes with the two closed immersions of the triples. -/
theorem categoricalPullbackHomZ_left_comp_i' {d e : FiniteEtaleCartesianTriple s}
    (φ : (finiteEtaleTripleToCategoricalPullback s).obj d ⟶
      (finiteEtaleTripleToCategoricalPullback s).obj e) :
    (categoricalPullbackHomZ φ).left ≫ e.1.i' = d.1.i' ≫ φ.snd.left :=
  ((congrArg ((categoricalPullbackHomZ φ).left ≫ ·)
      (finiteEtaleTripleIsoLeft_hom_left_fst e.1 e.2.1 e.2.2.2).symm).trans
    ((comp_baseChange_map_eq_iff s.i _ _ _ _).1
      (categoricalPullbackHomZ_comp_isoLeft φ).symm).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ φ.snd.left) (finiteEtaleTripleIsoLeft_hom_left_fst d.1 d.2.1 d.2.2.2)))

/-- The component over `Z` commutes with the two integral morphisms of the triples. -/
theorem categoricalPullbackHomZ_left_comp_j' {d e : FiniteEtaleCartesianTriple s}
    (φ : (finiteEtaleTripleToCategoricalPullback s).obj d ⟶
      (finiteEtaleTripleToCategoricalPullback s).obj e) :
    (categoricalPullbackHomZ φ).left ≫ e.1.j' = d.1.j' ≫ φ.fst.left :=
  ((congrArg ((categoricalPullbackHomZ φ).left ≫ ·)
      (finiteEtaleTripleIsoRight_hom_left_fst e.1 e.2.2.1 e.2.2.2).symm).trans
    ((comp_baseChange_map_eq_iff s.j _ _ _ _).1
      (categoricalPullbackHomZ_comp_isoRight φ).symm).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ φ.fst.left) (finiteEtaleTripleIsoRight_hom_left_fst d.1 d.2.2.1 d.2.2.2)))

/-- Reading a finite étale triple in the 2-fibre product is full: a pair of morphisms of covers
of `Y` and of `X` compatible over `Z` is a morphism of cartesian triples, its component over `Z`
being `AlgebraicGeometry.categoricalPullbackHomZ`. -/
instance finiteEtaleTripleToCategoricalPullback_full
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToCategoricalPullback s).Full where
  map_surjective φ :=
    ⟨{ x := φ.snd.left
       y := φ.fst.left
       z := (categoricalPullbackHomZ φ).left
       left := (categoricalPullbackHomZ_left_comp_i' φ).symm
       right := (categoricalPullbackHomZ_left_comp_j' φ).symm
       overX := MorphismProperty.Over.w φ.snd
       overY := MorphismProperty.Over.w φ.fst
       overZ := MorphismProperty.Over.w (categoricalPullbackHomZ φ) },
     CategoricalPullback.hom_ext (MorphismProperty.Over.Hom.ext rfl)
       (MorphismProperty.Over.Hom.ext rfl)⟩

/-- The cartesian diagram attached to an object of the 2-fibre product
`FÉt_Y ×_{FÉt_Z} FÉt_X`: its cover of `Z` is the base change along `j` of the cover of `Y`, and
the structural isomorphism identifies that with the base change along `i` of the cover of `X`,
which makes the square on the closed-immersion side cartesian. -/
noncomputable def cartesianDiagramOfCategoricalPullback
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    CartesianDiagram s :=
  have _hAf : IsFinite c.fst.hom := c.fst.prop.1
  have _hAe : Etale c.fst.hom := c.fst.prop.2
  have _hBf : IsFinite c.snd.hom := c.snd.prop.1
  have _hBe : Etale c.snd.hom := c.snd.prop.2
  have hh : finiteEtale (pullback.snd c.fst.hom s.j) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback c.fst.hom s.j) c.fst.prop
  have _hhf : IsFinite (pullback.snd c.fst.hom s.j) := hh.1
  have _hhe : Etale (pullback.snd c.fst.hom s.j) := hh.2
  { X' := c.snd.left
    Y' := c.fst.left
    Z' := pullback c.fst.hom s.j
    i' := c.iso.hom.left ≫ pullback.fst c.snd.hom s.i
    j' := pullback.fst c.fst.hom s.j
    f := c.snd.hom
    g := c.fst.hom
    h := pullback.snd c.fst.hom s.j
    left_isPullback :=
      IsPullback.of_iso_pullback
        ⟨(Category.assoc _ _ _).trans (finiteEtaleBaseChange_hom_left_fst_comp s.i c.iso.hom)⟩
        ((MorphismProperty.Over.forget finiteEtale (⊤ : MorphismProperty Scheme.{u}) s.Z ⋙
          CategoryTheory.Over.forget s.Z).mapIso c.iso) rfl
        (MorphismProperty.Over.w c.iso.hom)
    right_isPullback := IsPullback.of_hasPullback c.fst.hom s.j }

/-- The cover of `X` of the cartesian diagram attached to an object of the 2-fibre product is
finite étale. -/
theorem finiteEtale_cartesianDiagramOfCategoricalPullback_f
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    finiteEtale (cartesianDiagramOfCategoricalPullback c).f := c.snd.prop

/-- The cover of `Y` of the cartesian diagram attached to an object of the 2-fibre product is
finite étale. -/
theorem finiteEtale_cartesianDiagramOfCategoricalPullback_g
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    finiteEtale (cartesianDiagramOfCategoricalPullback c).g := c.fst.prop

/-- The cover of `Z` of the cartesian diagram attached to an object of the 2-fibre product is
finite étale, being a base change of the cover of `Y`. -/
theorem finiteEtale_cartesianDiagramOfCategoricalPullback_h
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    finiteEtale (cartesianDiagramOfCategoricalPullback c).h :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback c.fst.hom s.j) c.fst.prop

/-- The finite étale cartesian triple attached to an object of the 2-fibre product. -/
noncomputable abbrev finiteEtaleTripleOfCategoricalPullback
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    FiniteEtaleCartesianTriple s :=
  ⟨cartesianDiagramOfCategoricalPullback c,
    finiteEtale_cartesianDiagramOfCategoricalPullback_f c,
    finiteEtale_cartesianDiagramOfCategoricalPullback_g c,
    finiteEtale_cartesianDiagramOfCategoricalPullback_h c⟩

/-- For the triple attached to an object of the 2-fibre product the identification of its cover
of `Z` with the base change of its cover of `Y` is the identity, because that cover of `Z` was
chosen to be that base change. -/
theorem finiteEtaleTripleIsoRight_ofCategoricalPullback_hom_left
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    (finiteEtaleTripleIsoRight (cartesianDiagramOfCategoricalPullback c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_g c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_h c)).hom.left
      = 𝟙 (pullback c.fst.hom s.j) :=
  pullback.hom_ext
    ((finiteEtaleTripleIsoRight_hom_left_fst _ _ _).trans (Category.id_comp _).symm)
    ((MorphismProperty.Over.w _).trans (Category.id_comp _).symm)

/-- For the triple attached to an object of the 2-fibre product the identification of its cover
of `Z` with the base change of its cover of `X` is the structural isomorphism of that object. -/
theorem finiteEtaleTripleIsoLeft_ofCategoricalPullback
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    (finiteEtaleTripleIsoLeft (cartesianDiagramOfCategoricalPullback c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_f c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_h c)).hom =
      (finiteEtaleTripleIsoRight (cartesianDiagramOfCategoricalPullback c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_g c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_h c)).hom ≫ c.iso.hom :=
  finiteEtaleBaseChange_hom_ext s.i <|
    (finiteEtaleTripleIsoLeft_hom_left_fst _ _ _).trans <|
      (Category.id_comp (c.iso.hom.left ≫ pullback.fst c.snd.hom s.i)).symm.trans <|
        (congrArg (· ≫ c.iso.hom.left ≫ pullback.fst c.snd.hom s.i)
            (finiteEtaleTripleIsoRight_ofCategoricalPullback_hom_left c).symm).trans
          (comp_left_comp_fst s.i _ c.iso.hom).symm

/-- Reading the triple attached to an object of the 2-fibre product back in the 2-fibre product
recovers its structural isomorphism. -/
theorem finiteEtaleTripleToCategoricalPullback_obj_iso_hom
    (c : CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i)) :
    ((finiteEtaleTripleToCategoricalPullback s).obj
        (finiteEtaleTripleOfCategoricalPullback c)).iso.hom = c.iso.hom :=
  (congrArg ((finiteEtaleTripleIsoRight (cartesianDiagramOfCategoricalPullback c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_g c)
        (finiteEtale_cartesianDiagramOfCategoricalPullback_h c)).inv ≫ ·)
      (finiteEtaleTripleIsoLeft_ofCategoricalPullback c)).trans
    (Iso.inv_hom_id_assoc _ _)

/-- Reading a finite étale triple in the 2-fibre product is essentially surjective: an object of
`FÉt_Y ×_{FÉt_Z} FÉt_X` is read off the triple whose cover of `Z` is the base change along `j` of
its cover of `Y`. -/
instance finiteEtaleTripleToCategoricalPullback_essSurj
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToCategoricalPullback s).EssSurj where
  mem_essImage c :=
    ⟨finiteEtaleTripleOfCategoricalPullback c,
      ⟨CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
        ((congrArg (· ≫ c.iso.hom) ((finiteEtaleBaseChange s.j).map_id _)).trans <|
          (Category.id_comp _).trans <|
            (finiteEtaleTripleToCategoricalPullback_obj_iso_hom c).symm.trans <|
              (Category.comp_id _).symm.trans
                (congrArg (((finiteEtaleTripleToCategoricalPullback s).obj
                    (finiteEtaleTripleOfCategoricalPullback c)).iso.hom ≫ ·)
                  ((finiteEtaleBaseChange s.i).map_id _).symm))⟩⟩

/-- The pushout of finite étale cartesian triples is an equivalence onto the finite étale covers
of `Y ⨿_Z X`. -/
instance finiteEtaleTripleToOver_isEquivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToOver s).IsEquivalence := {}

/-- Reading a finite étale cartesian triple in the 2-fibre product
`FÉt_Y ×_{FÉt_Z} FÉt_X` is an equivalence. -/
instance finiteEtaleTripleToCategoricalPullback_isEquivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtaleTripleToCategoricalPullback s).IsEquivalence := {}

/-- **Stacks Project, Tag 0EK4.**  The restriction functor
`FÉt_{Y ⨿_Z X} ⟶ FÉt_Y ×_{FÉt_Z} FÉt_X` is an equivalence of categories.  Composed with the
pushout of finite étale cartesian triples, which is an equivalence by
[Stacks Project, Tag 0ECL], it is reading a triple in the 2-fibre product, which is an
equivalence; so it is one itself. -/
@[stacks 0EK4 "the restriction functor is an equivalence"]
instance finiteEtalePushoutRestriction_isEquivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtalePushoutRestriction s).IsEquivalence :=
  have : (finiteEtaleTripleToOver s ⋙ finiteEtalePushoutRestriction s).IsEquivalence :=
    Functor.isEquivalence_of_iso (finiteEtaleTripleToOverCompRestrictionIso s).symm
  Functor.isEquivalence_of_comp_left (finiteEtaleTripleToOver s)
    (finiteEtalePushoutRestriction s)

/-- **Stacks Project, Tag 0EK4.**  In the pushout situation of [Stacks Project, Tag 0ECI] — for
example when `Z ⟶ Y` and `Z ⟶ X` are closed immersions of schemes — there is an equivalence of
categories
`FÉt_{Y ⨿_Z X} ⟶ FÉt_Y ×_{FÉt_Z} FÉt_X`.
Its functor is `AlgebraicGeometry.finiteEtalePushoutRestriction`, which sends a finite étale
cover of the pushout to its base changes to `Y` and to `X` together with the canonical
identification of their restrictions to `Z`. -/
@[stacks 0EK4]
noncomputable def finiteEtalePushoutEquivalence
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    FiniteEtaleOver (pushoutScheme s) ≌
      CategoricalPullback (finiteEtaleBaseChange s.j) (finiteEtaleBaseChange s.i) :=
  (finiteEtalePushoutRestriction s).asEquivalence

/-- The equivalence of [Stacks Project, Tag 0EK4] is the restriction functor. -/
@[stacks 0EK4 "the comparison functor"]
theorem finiteEtalePushoutEquivalence_functor
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    (finiteEtalePushoutEquivalence s).functor = finiteEtalePushoutRestriction s := rfl

end Equivalence

end AlgebraicGeometry

end
