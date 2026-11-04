module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOne
import StacksCore.Tactic.StacksAttribute

/-!
# Rank one modules on an essentially small ringed site are invertible

Let `(C, J, O)` be a ringed site whose underlying category is essentially small in the universe
`w` of the sections of the structure sheaf. A sheaf of `O`-modules with sections in `w` which is
locally free of rank one is invertible, with no relation imposed between `w` and the universes
of the objects and the morphisms of `C`.

## Main definitions and results

* `AlgebraicGeometry.RingedSite.smallFunctor` and
  `AlgebraicGeometry.RingedSite.smallTopology`: the small model of the underlying site of an
  essentially small ringed site, as a dense subsite of it.
* `AlgebraicGeometry.RingedSite.isEquivalence_sheafPushforward_smallFunctor`: restriction of
  sheaves of abelian groups to that small model is an equivalence, with no size hypothesis.
* `AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall`:
  a module of rank one on an essentially small ringed site is invertible.

## Implementation notes

`AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one` proves the same
implication by exhibiting the dual `Hom_O(L, O)` of Tag 03EM, whose sections over `U` are indexed
by the objects of the slice `C/U`; that forces the sections of the module to lie in
`max u v w` for a site `C : Type u` with `Category.{v} C`. The small étale site of an algebraic
space is `RingedSite.{u + 1, u, u}`, so that form does not apply to it, and the present statement
is what its consumers need.

The route is to transport the question to a small model of the site, where the two universes of
the site are both `w` and the existing statement applies, and then to carry invertibility back.
Both transports are restriction of sections along the functor `v` of
`CategoryTheory.equivSmallModel`, which exhibits the small model as a dense subsite: the
comparison of the categories of modules is
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` and the compatibility with the tensor
product is `Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight`, both stated with the
four universes of the two sites and the module universe independent. The Comparison Lemma for
sheaves of abelian groups, which the first of these needs, comes for free because `v` is the
functor of an equivalence of categories: `CategoryTheory.Equivalence.sheafCongr` is an
equivalence of the sheaf categories with no size hypothesis, and its functor **is** the
restriction functor.

Three points of friction. The covering families of Tag 0409 are indexed in the maximum of the
object and the morphism universes of the site, so a covering family on `C` does not index one on
the small model; `exists_small_cover` replaces it by the family of *all* arrows into the object
over which the module is trivial, which is indexed in `w` because the small model is small and
still covers. Local freeness of rank one is stated by a colimit cofan on `Fin 1`, which is the
same thing as a single isomorphism — `isIso_cofanInj_of_isColimit` and
`isColimitCofanOfIsIso` — and an isomorphism travels along the restriction functor without any
preservation hypothesis, whereas a colimit would need one. Finally the restriction functor is
fully faithful for a dense subsite with no further hypothesis, so the tensor inverse is built
downstairs and its defining isomorphism is pulled back along full faithfulness rather than
constructed upstairs.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u₁ v₁ t

namespace AlgebraicGeometry.RingedSite

/-! ### One element coproduct cofans -/

section Cofan

variable {D : Type*} [Category* D]

/-- A one element family presenting `M` as a coproduct of copies of `A` consists of a single
isomorphism `A ≅ M`. -/
private lemma isIso_cofanInj_of_isColimit {A M : D} (ι : Fin 1 → (A ⟶ M))
    (h : IsColimit (Cofan.mk M ι)) : IsIso (ι 0) := by
  have hf : ι 0 ≫ h.desc (Cofan.mk A (fun _ : Fin 1 => 𝟙 A)) = 𝟙 A :=
    h.fac (Cofan.mk A (fun _ : Fin 1 => 𝟙 A)) ⟨0⟩
  refine ⟨h.desc (Cofan.mk A (fun _ : Fin 1 => 𝟙 A)), hf, ?_⟩
  refine h.hom_ext (fun j => ?_)
  obtain ⟨j⟩ := j
  fin_cases j
  show ι 0 ≫ _ ≫ ι 0 = ι 0 ≫ 𝟙 M
  rw [← Category.assoc, hf, Category.id_comp, Category.comp_id]

/-- An isomorphism `A ≅ M`, read as a one element family, presents `M` as a coproduct of one
copy of `A`. -/
private noncomputable def isColimitCofanOfIsIso {A M : D} (f : A ⟶ M) [IsIso f] :
    IsColimit (Cofan.mk M (fun _ : Fin 1 => f)) :=
  Cofan.IsColimit.mk _ (fun s => inv f ≫ s.inj 0) (fun s j => by fin_cases j; simp)
    (fun s m hm => by
      have hf : f ≫ m = s.inj 0 := hm 0
      rw [← hf, ← Category.assoc]
      simp)

end Cofan

/-! ### Restriction of a trivialization along a morphism of the site -/

section OverMap

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D}

/-- The restriction of a trivialized sheaf of modules to an object lying over the object where
it is trivialized is again trivial. -/
private noncomputable def isoUnitOverMap (R : Sheaf K RingCat.{w}) (M : SheafOfModules.{w} R)
    {A B : D} (h : B ⟶ A) (e : M.over A ≅ SheafOfModules.unit (R.over A)) :
    M.over B ≅ SheafOfModules.unit (R.over B) :=
  ((SheafOfModules.overFunctorMap R h).app M).symm ≪≫
    (SheafOfModules.overMap R h).mapIso e ≪≫ SheafOfModules.overMapUnitIso h

end OverMap

/-! ### Covering families transported to a small model of the site -/

section Cover

variable {C₀ : Type w} [SmallCategory C₀] {C : Type u₁} [Category.{v₁} C]

/-- A covering family of the image of an object `U` of a small site equivalent to `(C, J)`,
whose members satisfy a property after transport to the small site, produces a covering family
of `U` whose members satisfy that property and which is indexed in the universe of the small
site. The family produced is the family of *all* arrows into `U` whose source satisfies the
property. -/
private theorem exists_small_cover (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C)
    (ee : C₀ ≌ C) [ee.functor.IsCocontinuous J₀ J] {P : C₀ → Prop} (U : C₀) {I : Type t}
    (W : I → C) (g : ∀ i, W i ⟶ ee.functor.obj U)
    (hcov : Sieve.ofArrows W g ∈ J (ee.functor.obj U))
    (hP : ∀ i, P (ee.inverse.obj (W i))) :
    ∃ (I' : Type w) (V : I' → C₀) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J₀ U ∧ ∀ i, P (V i) := by
  refine ⟨Σ Z : C₀, {h : Z ⟶ U // P Z}, fun x => x.1, fun x => x.2.1, ?_, fun x => x.2.2⟩
  apply J₀.superset_covering _ (ee.functor.cover_lift J₀ J hcov)
  intro Z h hh
  replace hh : (Sieve.ofArrows W g).arrows (ee.functor.map h) := hh
  rw [Sieve.mem_ofArrows_iff] at hh
  rw [Sieve.mem_ofArrows_iff]
  obtain ⟨i, a, ha⟩ := hh
  refine ⟨⟨ee.inverse.obj (W i), ⟨ee.inverse.map (g i) ≫ (ee.unitIso.app U).inv, hP i⟩⟩,
    (ee.unitIso.app Z).hom ≫ ee.inverse.map a, ?_⟩
  have hnat := ee.unit.naturality h
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have key : ee.inverse.map a ≫ ee.inverse.map (g i) = ee.inverse.map (ee.functor.map h) := by
    rw [← Functor.map_comp, ha]
  simp only [Category.assoc]
  rw [← Category.assoc (ee.inverse.map a), key, ← Category.assoc,
    show (ee.unitIso.app Z).hom = ee.unit.app Z from rfl, ← hnat]
  simp

end Cover

/-! ### The small model of an essentially small ringed site -/

section SmallModel

variable (X : RingedSite.{u₁, v₁, w}) [EssentiallySmall.{w} X.C]

/-- The functor from a small model of the underlying site of `X` into that site. -/
noncomputable abbrev smallFunctor : SmallModel.{w} X.C ⥤ X.C :=
  (equivSmallModel.{w} X.C).inverse

/-- The topology on a small model of the underlying site of `X` induced by `X.J`. -/
noncomputable abbrev smallTopology : GrothendieckTopology (SmallModel.{w} X.C) :=
  (smallFunctor X).inducedTopology X.J

/-- The ringed site on a small model of the underlying site of `X`, with the direct image of
the structure sheaf of `X`. All three of its universes are the universe `w` of the sections of
the structure sheaf. -/
private noncomputable abbrev smallSite : RingedSite.{w, w, w} where
  C := SmallModel.{w} X.C
  J := smallTopology X
  O := ((smallFunctor X).sheafPushforwardContinuous CommRingCat.{w} (smallTopology X) X.J).obj X.O

/-- Localizing the comparison with the small model at an object again gives a dense subsite. -/
private instance overPost_isDenseSubsite (B : SmallModel.{w} X.C) :
    (Over.post (X := B) (smallFunctor X)).IsDenseSubsite ((smallTopology X).over B)
      (X.J.over ((smallFunctor X).obj B)) where
  functorPushforward_mem_iff := by
    intro Z S
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact (smallFunctor X).functorPushforward_mem_iff (smallTopology X) X.J

/-- Restriction of sheaves of modules from `X` to the small model. -/
private noncomputable abbrev restrictModules :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O) :=
  Stacks.DenseSubsiteModules.moduleRestriction (smallTopology X) X.J (smallFunctor X)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Restriction of sheaves of modules from the slice of `X` at `v B` to the slice of the small
model at `B`. -/
private noncomputable abbrev restrictModulesOver (B : SmallModel.{w} X.C) :
    SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((smallFunctor X).obj B)) ⥤
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).over B) :=
  Stacks.DenseSubsiteModules.moduleRestriction ((smallTopology X).over B)
    (X.J.over ((smallFunctor X).obj B)) (Over.post (X := B) (smallFunctor X))
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((smallFunctor X).obj B))

/-- Restricting a sheaf of modules to the small model and then to the slice at `B` is
restricting to the slice at `v B` and then to the small model. -/
private theorem restrictModules_obj_over
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : SmallModel.{w} X.C) :
    ((restrictModules X).obj L).over B =
      (restrictModulesOver X B).obj (L.over ((smallFunctor X).obj B)) := rfl

/-- A trivialization of `L` over `v B` restricts to a trivialization of the restriction of `L`
over `B`. -/
private noncomputable def isoUnitRestrictOver
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : SmallModel.{w} X.C)
    (e : L.over ((smallFunctor X).obj B) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((smallFunctor X).obj B))) :
    ((restrictModules X).obj L).over B ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).over B) :=
  (restrictModulesOver X B).mapIso e

/-- Restriction of sheaves of abelian groups to the small model is an equivalence: it is the
functor of `CategoryTheory.Equivalence.sheafCongr`, which needs no size hypothesis. -/
theorem isEquivalence_sheafPushforward_smallFunctor :
    ((smallFunctor X).sheafPushforwardContinuous AddCommGrpCat.{w}
      (smallTopology X) X.J).IsEquivalence :=
  ((equivSmallModel.{w} X.C).sheafCongr X.J (smallTopology X)
    AddCommGrpCat.{w}).isEquivalence_functor

/-- Restriction of sheaves of modules to the small model is essentially surjective, so every
sheaf of modules on the small model comes from one on `X`. -/
private theorem essSurj_restrictModules : (restrictModules X).EssSurj :=
  have := isEquivalence_sheafPushforward_smallFunctor X
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction (smallTopology X) X.J
    (smallFunctor X) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).EssSurj

/-- Restriction of sheaves of modules to a dense subsite is full. -/
private theorem full_restrictModules : (restrictModules X).Full :=
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction (smallTopology X) X.J
    (smallFunctor X) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Full

/-- Restriction of sheaves of modules to a dense subsite is faithful. -/
private theorem faithful_restrictModules : (restrictModules X).Faithful :=
  inferInstanceAs (Stacks.DenseSubsiteModules.moduleRestriction (smallTopology X) X.J
    (smallFunctor X) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Faithful

/-- Local freeness of rank one is carried to the small model: a trivializing covering family
of `v U` produces one of `U`, indexed in the universe of the small model. -/
private theorem isFiniteLocallyFreeOfRank_restrictModules
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : IsFiniteLocallyFreeOfRank X L 1) :
    IsFiniteLocallyFreeOfRank (smallSite X) ((restrictModules X).obj L) 1 := by
  have : ((equivSmallModel.{w} X.C).symm).functor.IsCocontinuous (smallTopology X) X.J :=
    inferInstanceAs ((smallFunctor X).IsCocontinuous (smallTopology X) X.J)
  intro U
  obtain ⟨I, V, f, hcov, hfree⟩ := hL ((smallFunctor X).obj U)
  refine exists_small_cover (smallTopology X) X.J ((equivSmallModel.{w} X.C).symm)
    (P := fun B => ∃ ι : ∀ _ : Fin 1,
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).over B) ⟶
          ((restrictModules X).obj L).over B,
      Nonempty (IsColimit (Cofan.mk (((restrictModules X).obj L).over B) ι)))
    U V f hcov (fun i => ?_)
  obtain ⟨ι, ⟨hι⟩⟩ := hfree i
  have := isIso_cofanInj_of_isColimit ι hι
  let B : SmallModel.{w} X.C := (equivSmallModel.{w} X.C).functor.obj (V i)
  let e : L.over ((smallFunctor X).obj B) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((smallFunctor X).obj B)) :=
    isoUnitOverMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) L
      ((equivSmallModel.{w} X.C).unitIso.app (V i)).inv (asIso (ι 0)).symm
  exact ⟨fun _ => (isoUnitRestrictOver X L B e).inv, ⟨isColimitCofanOfIsIso _⟩⟩

end SmallModel

/-! ### Transporting the tensor inverse back from the small model -/

section Tensor

variable (X : RingedSite.{u₁, v₁, w}) [EssentiallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction to the small model carries the tensor product to the tensor product. -/
private noncomputable def restrictModules_tensorLeftFunctor_obj
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (restrictModules X).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨X.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.O.obj) (forget₂ CommRingCat RingCat)
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)⟩).obj (L))).obj N) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
          ⟨(smallSite X).O.obj, Presheaf.isSheaf_of_isSheaf_comp _ ((smallSite X).O.obj)
            (forget₂ CommRingCat RingCat)
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).property)⟩).obj
          (((restrictModules X).obj L)))).obj
        ((restrictModules X).obj N) :=
  letI : X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
    X.hasSheafCompose_forget₂_ringCat
  letI : (smallTopology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
    (smallSite X).hasSheafCompose_forget₂_ringCat
  (Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight (smallTopology X) X.J
    (smallFunctor X) X.O N).app L

end Tensor

/-! ### The theorem -/

/-- **Stacks Project, Tag 0B8M**, clause 1, on an essentially small ringed site. A sheaf of
modules which is locally free of rank one is invertible, with the universe of the sections of
the structure sheaf independent of the universes of the site. -/
@[stacks 0B8M "locally free of rank one implies invertible, on an essentially small site"]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
    (X : AlgebraicGeometry.RingedSite.{u₁, v₁, w}) [EssentiallySmall.{w} X.C]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1) :
    Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L := by
  have := essSurj_restrictModules X
  have := full_restrictModules X
  have := faithful_restrictModules X
  have h₀ : Stacks.SheafOfModules.IsInvertible (smallSite X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).property
      ((restrictModules X).obj L) :=
    isInvertible_of_isFiniteLocallyFreeOfRank_one.{w, w, w} (smallSite X)
      ((restrictModules X).obj L) (isFiniteLocallyFreeOfRank_restrictModules X L hL)
  obtain ⟨N₀, ⟨e₀⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := (smallSite X).O.obj)
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).property)
    ((restrictModules X).obj L)).mp h₀
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.O.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) L).mpr
    ⟨(restrictModules X).objPreimage N₀, ⟨(restrictModules X).preimageIso ?_⟩⟩
  exact restrictModules_tensorLeftFunctor_obj X L ((restrictModules X).objPreimage N₀) ≪≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
      ⟨(smallSite X).O.obj, Presheaf.isSheaf_of_isSheaf_comp _ ((smallSite X).O.obj)
        (forget₂ CommRingCat RingCat)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallSite X).O).property)⟩).obj
      (((restrictModules X).obj L)))).mapIso ((restrictModules X).objObjPreimageIso N₀) ≪≫ e₀

end AlgebraicGeometry.RingedSite

end
