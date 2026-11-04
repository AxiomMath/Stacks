module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesSmall

/-!
# Stackification and sheaves of modules, in every universe (Stacks 06WR)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`.  Stacks 06WR asserts that if `f` induces an equivalence of stackifications, then
the inverse image `f^*` of Stacks 06WE is an equivalence `Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` and restricts to
an equivalence `QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`.

Here the two fibred categories have their objects in independent universes and their morphisms
in a common universe `w`, and the modules have their sections in any universe containing the
universe `u` of the rings of the big fppf site.

## Main definitions

* `CategoryTheory.Functor.toInducedCategory`: a functor `F : C ⥤ D` read as a functor into the
  category induced by `D` on the objects of `C`, so that `F` is the composite of it with the
  fully faithful `CategoryTheory.inducedFunctor`.
* `AlgebraicGeometry.Stack.inducedCategoryTopology`: the fppf topology of that induced category.

## Main results

All three are in the namespace `AlgebraicGeometry.Stack`.

* `isEquivalence_sheafPushforwardContinuous_of_isStackificationEquivalence`:
  restriction of abelian sheaves along `f` is an equivalence.
* `isEquivalence_modulePullback_of_isStackificationEquivalence_anyUniverse`:
  **Stacks 06WR, the `Mod` clause.**
* `isEquivalence_quasicoherentPullback_of_isStackificationEquivalence_anyUniverse`:
  **Stacks 06WR, the `QCoh` clause.**

## Implementation notes

The source reduces to the case where `𝒴` is the stackification of `𝒳` and cites Stacks 06WQ.
Here `f` is factored as `𝒳 ⥤ 𝒵 ⥤ 𝒴`, where `𝒵` is the category induced by `𝒴` on the objects
of `𝒳`: it is fibred in groupoids, the second functor is fully faithful and covers `𝒴`, and the
first is the identity on objects and, by the two local criteria of Stacks 02ZN, locally full
and locally faithful.  Each factor has, for every object, a `1`-hypercover by objects of its
source indexed by types in `Type u`: for the second because `𝒴` has fibre products
(Stacks 06WY) and the base is essentially small, for the first with a single object and a single
arrow, since a pair of parallel arrows with the same image agrees locally.  So restriction of
abelian sheaves along each factor is an equivalence as soon as abelian groups have limits of
size `u` (`CategoryTheory.Functor.isEquivalence_of_isOneHypercoverDense`), which needs no bound
on the size of `𝒳` or of `𝒴`; the Comparison Lemma for sheaves of modules then lifts it to
modules.  The base declarations in
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModules` ask instead for `𝒳` and `𝒴`
to have objects and morphisms in `Type u`.

## References

* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory

universe u v₁ v₂ w m u₃ v₃ u₄ v₄

namespace CategoryTheory.Functor

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- A functor `F : C ⥤ D` read as a functor into the category induced by `D` on the objects of
`C`: it is the identity on objects, and `F` is its composite with the fully faithful functor
`CategoryTheory.inducedFunctor F.obj`. -/
@[simps]
def toInducedCategory (F : C ⥤ D) : C ⥤ InducedCategory D F.obj where
  obj X := X
  map φ := InducedCategory.homMk (F.map φ)

/-- `F` is the composite of `CategoryTheory.Functor.toInducedCategory F` with the inclusion of the
induced category. -/
def toInducedCategoryCompInducedFunctorIso (F : C ⥤ D) :
    F.toInducedCategory ⋙ inducedFunctor F.obj ≅ F :=
  Iso.refl _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w} 𝒳] {𝒴 : Type v₂} [Category.{w} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)

include hp hq hF in
/-- The category induced by `𝒴` on the objects of `𝒳` is fibred in groupoids over the base: lifts
of base arrows come from `𝒳`, and their uniqueness from `𝒴`. -/
theorem isFiberedInGroupoids_inducedFunctor_comp :
    (inducedFunctor f.obj ⋙ q).IsFiberedInGroupoids where
  exists_lift {V U} a x hx := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift a x (by rwa [← hF.comp_eq])
    refine ⟨y, InducedCategory.homMk (f.map φ), ?_⟩
    have : (f ⋙ q).IsHomLift a φ := by rwa [hF.comp_eq]
    exact (Functor.isHomLift_comp_iff (inducedFunctor f.obj) q a _).2
      ((Functor.isHomLift_comp_iff f q a φ).1 this)
  unique_lift {x y z} φ ψ a ha := by
    obtain ⟨χ, ⟨h₁, h₂⟩, huniq⟩ := hq.unique_lift φ.hom ψ.hom a ha
    exact ⟨InducedCategory.homMk χ, ⟨h₁, InducedCategory.hom_ext h₂⟩, fun γ hγ =>
      InducedCategory.hom_ext (huniq γ.hom ⟨hγ.1, congrArg InducedCategory.Hom.hom hγ.2⟩)⟩

include hp hq hF in
/-- The first factor `𝒳 ⥤ 𝒵` of `f` is a 1-morphism of fibred categories. -/
theorem isFibredOneMorphism_toInducedCategory :
    p.IsFibredOneMorphism (inducedFunctor f.obj ⋙ q) f.toInducedCategory :=
  (isFiberedInGroupoids_inducedFunctor_comp B S hS p q hp hq f hF).isFibredOneMorphism
    hF.comp_eq

/-- The fppf topology of the category induced by `𝒴` on the objects of `𝒳`, the middle term of the
factorization `𝒳 ⥤ 𝒵 ⥤ 𝒴` of `f`. -/
abbrev inducedCategoryTopology : GrothendieckTopology (InducedCategory 𝒴 f.obj) :=
  associatedTopology B S hS (inducedFunctor f.obj ⋙ q) B.topology

section Equivalence

variable {B S hS p q hp hq f hF}

include hp hq in
/-- The first factor `𝒳 ⥤ 𝒵` of a 1-morphism inducing an equivalence of stackifications is a dense
subsite inclusion: it is the identity on objects, and the two local criteria of Stacks 02ZN make
it locally full and locally faithful. -/
theorem isDenseSubsite_toInducedCategory
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    f.toInducedCategory.IsDenseSubsite (associatedTopology B S hS p B.topology)
      (inducedCategoryTopology B S hS q f) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  have hr := isFiberedInGroupoids_inducedFunctor_comp B S hS p q hp hq f hF
  let : (inducedFunctor f.obj ⋙ q).IsFibered := hr.isFibered
  have hj := isFibredOneMorphism_toInducedCategory B S hS p q hp hq f hF
  let J := associatedTopology B S hS p B.topology
  let : f.toInducedCategory.IsContinuous J (inducedCategoryTopology B S hS q f) :=
    (hj.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).1
  let : f.toInducedCategory.IsCocontinuous J (inducedCategoryTopology B S hS q f) :=
    (hj.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).2
  let : f.toInducedCategory.IsCoverDense (inducedCategoryTopology B S hS q f) :=
    ⟨fun Z => (inducedCategoryTopology B S hS q f).superset_covering
      (fun Y g _ => ⟨{ obj := Y, lift := 𝟙 _, map := g, fac := Category.id_comp g }⟩)
      ((inducedCategoryTopology B S hS q f).top_mem Z)⟩
  refine Functor.isDenseSubsite_of_isCocontinuous f.toInducedCategory J
    (inducedCategoryTopology B S hS q f)
    (CoverPreserving.of_isContinuous _ J (inducedCategoryTopology B S hS q f))
    (fun U' U a b hab => ?_) (fun U' U c => ?_)
  · exact Functor.IsFibredOneMorphism.equalizerSieve_mem_inheritedTopology'
      (B.topology.over (B.obj hS)) hp hq hF heq a b (congrArg InducedCategory.Hom.hom hab)
  · refine J.superset_covering (fun Z g hg => ?_)
      (Functor.IsFibredOneMorphism.imageSieve_mem_inheritedTopology'
        (B.topology.over (B.obj hS)) hp hF heq c.hom)
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, InducedCategory.hom_ext ht⟩

include hp hq in
/-- The first factor `𝒳 ⥤ 𝒵` is `1`-hypercover dense: every object of `𝒵` is an object of `𝒳`, and
two parallel arrows of `𝒳` with the same image in `𝒵` agree along a covering sieve. -/
theorem isOneHypercoverDense_toInducedCategory
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    Functor.IsOneHypercoverDense.{u} f.toInducedCategory
      (associatedTopology B S hS p B.topology) (inducedCategoryTopology B S hS q f) where
  nonempty_oneHypercoverDenseData Z := by
    let : p.IsFibered := hp.isFibered
    let : q.IsFibered := hq.isFibered
    obtain ⟨x, rfl⟩ : ∃ x : 𝒳, f.toInducedCategory.obj x = Z := ⟨Z, rfl⟩
    refine ⟨{
      I₀ := PUnit
      X _ := x
      f _ := 𝟙 _
      I₁ _ _ := PUnit
      Y _ _ _ := x
      p₁ _ _ _ := 𝟙 x
      p₂ _ _ _ := 𝟙 x
      w _ _ _ := rfl
      mem₀ := ?_
      mem₁₀ := ?_ }⟩
    · refine (inducedCategoryTopology B S hS q f).superset_covering
        (fun Y g _ => ?_)
        ((inducedCategoryTopology B S hS q f).top_mem _)
      exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, g, (Category.comp_id g).symm⟩
    · intro _ _ W₀ p₁ p₂ hw
      have hw' : f.map p₁ = f.map p₂ := by
        rw [Category.comp_id, Category.comp_id] at hw
        exact congrArg InducedCategory.Hom.hom hw
      refine (associatedTopology B S hS p B.topology).superset_covering (fun T g hg => ?_)
        (Functor.IsFibredOneMorphism.equalizerSieve_mem_inheritedTopology'
          (B.topology.over (B.obj hS)) hp hq hF heq p₁ p₂ hw')
      exact ⟨PUnit.unit, g ≫ p₁, by simp, by simpa using hg.symm⟩

include hp hq in
/-- Restriction of abelian sheaves along a 1-morphism of categories fibred in groupoids which
induces an equivalence of stackifications is an equivalence, for abelian groups in every universe
containing `u`. -/
theorem isEquivalence_sheafPushforwardContinuous_of_isStackificationEquivalence
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      (B.topology.over (B.obj hS))).1
    (f.sheafPushforwardContinuous AddCommGrpCat.{max u m}
      (associatedTopology B S hS p B.topology)
      (associatedTopology B S hS q B.topology)).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  have hr := isFiberedInGroupoids_inducedFunctor_comp B S hS p q hp hq f hF
  let : (inducedFunctor f.obj ⋙ q).IsFibered := hr.isFibered
  let J := associatedTopology B S hS p B.topology
  let K := associatedTopology B S hS q B.topology
  let : f.IsContinuous J K :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).1
  have := B.essentiallySmall_schemes
  have := essentiallySmall_bigFppfOver B S hS
  have hloc : ∀ y : 𝒴, ∃ (I : Type u) (x : I → InducedCategory 𝒴 f.obj)
      (g : ∀ i, (inducedFunctor f.obj).obj (x i) ⟶ y), Sieve.ofArrows _ g ∈ K y := fun y =>
    hF.exists_ofArrows_mem_inheritedTopology (BigFppfOver.topology B S hS) hq heq.2 y
  let : (inducedFunctor f.obj).IsDenseSubsite (inducedCategoryTopology B S hS q f) K :=
    isDenseSubsite_of_full_of_faithful B S hS _ q hr hq (inducedFunctor f.obj) rfl
      (isCoverDense_of_forall_exists_ofArrows_mem B S hS q _ hloc)
  let : f.toInducedCategory.IsDenseSubsite J (inducedCategoryTopology B S hS q f) :=
    isDenseSubsite_toInducedCategory (hp := hp) (hq := hq) heq
  have : Limits.HasPullbacks 𝒴 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS q hq
  have : Functor.IsOneHypercoverDense.{u} (inducedFunctor f.obj)
      (inducedCategoryTopology B S hS q f) K :=
    Functor.IsOneHypercoverDense.of_hasPullbacks hloc
  have : Functor.IsOneHypercoverDense.{u} f.toInducedCategory J
      (inducedCategoryTopology B S hS q f) :=
    isOneHypercoverDense_toInducedCategory (hp := hp) (hq := hq) heq
  have : ((inducedFunctor f.obj).sheafPushforwardContinuous AddCommGrpCat.{max u m}
      (inducedCategoryTopology B S hS q f) K).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _
  have : (f.toInducedCategory.sheafPushforwardContinuous AddCommGrpCat.{max u m}
      J (inducedCategoryTopology B S hS q f)).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _
  exact inferInstanceAs ((inducedFunctor f.obj).sheafPushforwardContinuous AddCommGrpCat.{max u m}
      (inducedCategoryTopology B S hS q f) K ⋙
      f.toInducedCategory.sheafPushforwardContinuous AddCommGrpCat.{max u m}
      J (inducedCategoryTopology B S hS q f)).IsEquivalence

include hp hq in
/-- **Stacks 06WR, the `Mod` clause.**  Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`.  If `f` induces an equivalence of stackifications,
then the inverse image of sheaves of modules of Stacks 06WE is an equivalence
`Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`, for modules with sections in any universe containing `u`.

`f` is a dense subsite inclusion for the associated fppf topologies (Stacks 06WQ), restriction of
abelian sheaves along it is an equivalence
(`isEquivalence_sheafPushforwardContinuous_of_isStackificationEquivalence`), and the structure
sheaf of `𝒳` is the restriction along `f` of that of `𝒴`, so the Comparison Lemma for sheaves of
modules applies. -/
@[stacks 06WR "the Mod clause: f^* is an equivalence Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳), for categories fibred \
in groupoids in arbitrary universes and modules in any universe containing that of the rings"]
theorem isEquivalence_modulePullback_of_isStackificationEquivalence_anyUniverse
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    (modulePullback.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let : f.IsDenseSubsite (associatedTopology B S hS p B.topology)
      (associatedTopology B S hS q B.topology) :=
    hF.isDenseSubsite_of_isStackificationEquivalence' (BigFppfOver.topology B S hS) hp hq heq
  have := isEquivalence_sheafPushforwardContinuous_of_isStackificationEquivalence.{u, v₁, v₂, w, m}
    (hp := hp) (hq := hq) heq
  exact isEquivalence_pushforward_eqToHom'.{u, max u m, v₁, w, v₂, w} f _ _
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hF.comp_eq B.topology le_rfl)

include hp hq in
/-- **Stacks 06WR, the `QCoh` clause.**  Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`.  If `f` induces an equivalence of stackifications,
then the inverse image of quasi-coherent modules is an equivalence `QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`, for
modules with sections in any universe containing `u`.

Fullness and faithfulness come from the `Mod` clause, since `QCoh` is a full subcategory;
essential surjectivity needs in addition that `f^*` reflects quasi-coherence, which holds because
`f` is cover-dense (`AlgebraicGeometry.Stack.isQuasicoherentOnSite_of_modulePullback'`). -/
@[stacks 06WR "the QCoh clause: f^* is an equivalence QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳), for categories \
fibred in groupoids in arbitrary universes and modules in any universe containing that of the \
rings"]
theorem isEquivalence_quasicoherentPullback_of_isStackificationEquivalence_anyUniverse
    (heq : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      hF.IsStackificationEquivalence' (BigFppfOver.topology B S hS)) :
    (quasicoherentPullback'.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f
      hF.comp_eq).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  have hL :=
    isEquivalence_modulePullback_of_isStackificationEquivalence_anyUniverse.{u, v₁, v₂, w, m}
    (hp := hp) (hq := hq) heq
  let L := modulePullback.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f hF.comp_eq
    B.topology le_rfl
  let ι := (SheafOfModules.isQuasicoherentOnSite.{v₂, w, u, max u m}
    (ringStructureSheafCore B S hS q hq B.topology le_rfl)).ι
  let ι' := (SheafOfModules.isQuasicoherentOnSite.{v₁, w, u, max u m}
    (ringStructureSheafCore B S hS p hp B.topology le_rfl)).ι
  let Q := quasicoherentPullback'.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f hF.comp_eq
  have : L.Faithful := hL.faithful
  have : L.Full := hL.full
  have : L.EssSurj := hL.essSurj
  have : (Q ⋙ ι').Faithful := inferInstanceAs (ι ⋙ L).Faithful
  have hfaithful : Q.Faithful := Functor.Faithful.of_comp Q ι'
  have hfull : Q.Full := ⟨fun {M N} g => ⟨ObjectProperty.homMk (L.preimage g.hom),
    ObjectProperty.hom_ext _ (L.map_preimage g.hom)⟩⟩
  have hess : Q.EssSurj := by
    refine ⟨fun N => ?_⟩
    let N' : SheafOfModules.{max u m} (ringStructureSheafCore B S hS p hp B.topology le_rfl) :=
      N.obj
    have e : L.obj (L.objPreimage N') ≅ N' := L.objObjPreimageIso N'
    have hLM : (L.obj (L.objPreimage N')).IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm N.property
    exact ⟨⟨_, isQuasicoherentOnSite_of_modulePullback' B S hS p q hp hq f hF.comp_eq
      (Functor.IsFibredOneMorphism.isCoverDense_of_isStackificationEquivalence'
        (BigFppfOver.topology B S hS) hq hF heq) _ hLM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact Functor.IsEquivalence.mk

end Equivalence

end AlgebraicGeometry.Stack

end
