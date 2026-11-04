module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.SmallObject.Construction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Size.BoundedSizeObjects
public import StacksFrontier.Homology.Injectives.KInjective.SmallAcyclicComplexes
public import StacksFrontier.Homology.Injectives.KInjective.Criterion

/-!
# Functorial K-injective resolutions in Grothendieck abelian categories

Every cochain complex in a Grothendieck abelian category embeds termwise and
quasi-isomorphically into a complex of injective objects which is K-injective, and these
resolutions may be chosen functorially ([Stacks, Tag 079P]).

## Main definitions

* `Stacks.Injectives.KInjectiveResolution.FunctorialKInjectiveResolution` packages a functorial
  K-injective
  resolution: the endofunctor of `CochainComplex C ℤ`, the natural inclusion, and its
  four properties.
* `Stacks.Injectives.KInjectiveResolution.FunctorialInjectiveResolution` packages the conclusion of
  [Stacks, Tag 079N], the functorial injective enlargement which the construction
  iterates.

## Main results

* `exists_functorial_quasiIso_isKInjective_of_functorialInjectiveResolution`:
  a functorial injective enlargement gives rise to a functorial K-injective resolution.

## Implementation notes

The construction is the transfinite iteration of the composite successor operation
`M ↦ N(F(M))`, where `F` kills, up to homotopy, every map out of a fixed set of
bounded-above acyclic complexes of bounded size (the small-object construction applied
to the cells `K i ⟶ Cone(𝟙 (K i))`, with the representatives supplied by
[Stacks, Tag 079E] and [Stacks, Tag 079K]), and `N` is the functorial injective
enlargement of [Stacks, Tag 079N].  The iteration is run to a regular cardinal `κ`
larger than the size bound, the index set of representatives, and the size of the
separator.  The three properties of the inclusion into the iterate — quasi-isomorphism,
termwise monomorphism, injective terms — are proved stage by stage, the last by the
presentability argument of `iterateCompositeFunctor_term_injective`, and K-injectivity
of the result is read off from the criterion of [Stacks, Tag 079L].

**The Tag 079N datum is a hypothesis here, not a theorem.**  The source discharges it by
a separate construction (`M ↦ Cone(J(M) → Q(M))[-1]` for the degreewise injective
enlargement `J`); that construction is not available in this library, so
[Stacks, Tag 079N] appears as the explicit argument
`NR : FunctorialInjectiveResolution C`.  Consequently the chosen resolution functor and
the four properties of its inclusion, which the source states unconditionally, are not
defined here: they require Tag 079N to be discharged first.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 079N](https://stacks.math.columbia.edu/tag/079N)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe w v u

namespace Stacks.Injectives.KInjectiveResolution

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A functorial K-injective resolution: an endofunctor on cochain complexes together with a
natural inclusion of the identity into it which is a quasi-isomorphism and a degreewise
monomorphism, such that every value is a K-injective complex with injective terms. -/
structure FunctorialKInjectiveResolution where
  /-- The K-injective resolution endofunctor. -/
  functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural inclusion into the resolution. -/
  inclusion : Functor.id (CochainComplex C ℤ) ⟶ functor
  /-- The inclusion is a quasi-isomorphism. -/
  quasiIso (M : CochainComplex C ℤ) : QuasiIso (inclusion.app M)
  /-- The inclusion is a monomorphism in every degree. -/
  mono_f (M : CochainComplex C ℤ) (n : ℤ) : Mono ((inclusion.app M).f n)
  /-- Every term of the resolution is an injective object. -/
  injective (M : CochainComplex C ℤ) (n : ℤ) : Injective ((functor.obj M).X n)
  /-- The resolution is a K-injective complex. -/
  isKInjective (M : CochainComplex C ℤ) : (functor.obj M).IsKInjective

/-- The data and properties of a functorial injective enlargement of cochain
complexes: the conclusion of [Stacks, Tag 079N].  A functor on cochain complexes
together with a natural inclusion which is a degreewise monomorphism and a
quasi-isomorphism, and which in each degree factors through an injective
subobject of the corresponding term of the enlargement. -/
structure FunctorialInjectiveResolution where
  /-- The functorial enlargement of a complex. -/
  functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural map from a complex to its enlargement. -/
  inclusion : Functor.id (CochainComplex C ℤ) ⟶ functor
  /-- The inclusion is a monomorphism in every degree. -/
  mono_f : ∀ (M : CochainComplex C ℤ) (n : ℤ), Mono ((inclusion.app M).f n)
  /-- The inclusion is a quasi-isomorphism. -/
  quasiIso : ∀ M : CochainComplex C ℤ, QuasiIso (inclusion.app M)
  /-- In each degree the inclusion factors through an injective subobject of
  the corresponding term of the enlargement. -/
  factors_through_injective_subobject :
    ∀ (M : CochainComplex C ℤ) (n : ℤ),
      ∃ (I : C), Injective I ∧
        ∃ (toI : M.X n ⟶ I) (into : I ⟶ (functor.obj M).X n),
          Mono into ∧ toI ≫ into = (inclusion.app M).f n

variable [IsGrothendieckAbelian.{w} C]

/-- The functorial injective enlargement from Tag 079N, used as the second
successor operation in the K-injective construction. -/
private noncomputable def functorialInjectiveStep
    (NR : FunctorialInjectiveResolution C) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  NR.functor

/-- The natural map into the functorial injective enlargement. -/
private noncomputable def functorialInjectiveStepInclusion
    (NR : FunctorialInjectiveResolution C) :
    𝟭 (CochainComplex C ℤ) ⟶ functorialInjectiveStep C NR :=
  NR.inclusion

omit [IsGrothendieckAbelian.{w} C] in
/-- The natural map into the functorial injective enlargement is a
monomorphism in every degree. -/
private theorem functorialInjectiveStepInclusion_mono
    (NR : FunctorialInjectiveResolution C)
    (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (((functorialInjectiveStepInclusion C NR).app M).f n) :=
  NR.mono_f M n

omit [IsGrothendieckAbelian.{w} C] in
/-- The natural map into the functorial injective enlargement is a
quasi-isomorphism. -/
private theorem functorialInjectiveStepInclusion_quasiIso
    (NR : FunctorialInjectiveResolution C)
    (M : CochainComplex C ℤ) :
    QuasiIso ((functorialInjectiveStepInclusion C NR).app M) :=
  NR.quasiIso M

omit [IsGrothendieckAbelian.{w} C] in
/-- The natural map into the functorial injective enlargement is a
monomorphism of complexes. -/
private theorem functorialInjectiveStepInclusion_mono_complex
    (NR : FunctorialInjectiveResolution C)
    (M : CochainComplex C ℤ) :
    Mono ((functorialInjectiveStepInclusion C NR).app M) :=
  HomologicalComplex.mono_of_mono_f _ (functorialInjectiveStepInclusion_mono C NR M)

/-- In the iteration of a natural transformation, the legs of the colimit cocone at `j` and at
`Order.succ j` are related through the `j`th step. -/
private theorem iterationCocone_ι_app_eq
    {D : Type*} [Category D] {Φ : D ⥤ D} (ε : 𝟭 D ⟶ Φ)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J (D ⥤ D)] (j : J) (hj : ¬ IsMax j) (X : D) :
    (((SmallObject.SuccStruct.ofNatTrans ε).iterationCocone J).ι.app j).app X =
      ε.app (((SmallObject.SuccStruct.ofNatTrans ε).iterationFunctor J).obj j |>.obj X) ≫
        ((SmallObject.SuccStruct.ofNatTrans ε).iterationFunctorObjSuccIso j hj).inv.app X ≫
          (((SmallObject.SuccStruct.ofNatTrans ε).iterationCocone J).ι.app
            (Order.succ j)).app X := by
  have h := ((SmallObject.SuccStruct.ofNatTrans ε).iterationCocone J).w
    (homOfLE (Order.le_succ j))
  rw [← h]
  rw [SmallObject.SuccStruct.iterationFunctor_map_succ _ j hj]
  simp only [NatTrans.comp_app, Category.assoc]
  rfl

/-- Every term of the transfinite iterate of the composite successor operation
is an injective object.  This is the presentability argument at the heart of
Tag 079P: a map out of a subobject of the separator factors through a stage, at
which point the Tag 079N factorization through an injective subobject supplies
the required extension. -/
private theorem iterateCompositeFunctor_term_injective
    [IsGrothendieckAbelian.{w} (CochainComplex C ℤ)]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} (CochainComplex C ℤ)]
    (NR : FunctorialInjectiveResolution C)
    (M : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (ηM : 𝟭 (CochainComplex C ℤ) ⟶ M)
    (hM : ∀ X, Mono (ηM.app X))
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [NoMaxOrder κ.ord.ToType] [IsCardinalFiltered κ.ord.ToType κ]
    (G : C) (hG : IsSeparator G)
    (hGcard : Cardinal.mk (Shrink.{w} (Subobject G)) < κ)
    (Base : CochainComplex C ℤ) (n : ℤ) :
    Injective (((iterateCompositeFunctor M (functorialInjectiveStep C NR) ηM
      (functorialInjectiveStepInclusion C NR) κ).obj Base).X n) := by
  let D := CochainComplex C ℤ
  let N := NR.functor
  let ηN := NR.inclusion
  let η := composeFunctorialInclusions M N ηM ηN
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  let T := S.iterationFunctor κ.ord.ToType
  let E := (CategoryTheory.evaluation D D).obj Base ⋙
    HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let F := T ⋙ E
  let c : Cocone F := E.mapCocone (S.iterationCocone κ.ord.ToType)
  have hc : IsColimit c :=
    isColimitOfPreserves E (S.isColimitIterationCocone κ.ord.ToType)
  have htransition : ∀ (i j : κ.ord.ToType) (f : i ⟶ j), Mono (F.map f) := by
    intro i j f
    dsimp [F, E, T]
    have hmono : Mono (((S.iterationFunctor κ.ord.ToType).map f).app Base) :=
      iterateFunctorialStepMap_mono (M ⋙ N) η
        (fun Z => composeFunctorialInclusions_mono M N ηM ηN hM
          (fun Z => functorialInjectiveStepInclusion_mono_complex C NR Z) Z)
        κ i j f Base
    show Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (((S.iterationFunctor κ.ord.ToType).map f).app Base))
    exact (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_mono _
  let : ∀ (i j : κ.ord.ToType) (f : i ⟶ j), Mono (F.map f) := htransition
  have hGsmall : HasCardinalLT (Subobject G) κ :=
    (hasCardinalLT_iff_of_equiv (equivShrink.{w} (Subobject G)) κ).2
      ((hasCardinalLT_iff_cardinal_mk_lt _ _).2 hGcard)
  have hgen : (IsGrothendieckAbelian.generatingMonomorphisms G).rlp
      (0 : (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n) ⟶ 0) := by
    show ∀ ⦃A B : C⦄ (i : A ⟶ B),
      IsGrothendieckAbelian.generatingMonomorphisms G i →
        HasLiftingProperty i (0 : (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n) ⟶ 0)
    intro A B i hi
    change MorphismProperty.ofHoms (fun S : Subobject G => S.arrow) i at hi
    rcases hi with ⟨ASub⟩
    have hSsmall : HasCardinalLT (Subobject (ASub : C)) κ :=
      hGsmall.of_injective _ (Subobject.map_obj_injective ASub.arrow)
    have hSextend : ∀ (f : (ASub : C) ⟶ (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n)),
        ∃ (g : G ⟶ (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n)),
          ASub.arrow ≫ g = f := by
      intro f
      obtain ⟨j, g, rfl⟩ := IsGrothendieckAbelian.IsPresentable.surjectivity hc hSsmall f
      let Z := (T.obj j).obj Base
      obtain ⟨I, hI, toI, into, hinto, hfactor⟩ :=
        NR.factors_through_injective_subobject (M.obj Z) n
      change toI ≫ into = (ηN.app (M.obj Z)).f n at hfactor
      let : Injective I := hI
      let u := homOfLE (Order.le_succ j : j ≤ Order.succ j)
      have hj : ¬ IsMax j := not_isMax j
      let e := S.iterationFunctorObjSuccIso j hj
      let α := Functor.associator (T.obj j) M N
      let leg := (α.hom.app Base).f n ≫ (e.inv.app Base).f n ≫
        c.ι.app (Order.succ j)
      let a := Injective.factorThru (g ≫ (ηM.app Z).f n ≫ toI) ASub.arrow
      refine ⟨a ≫ into ≫ leg, ?_⟩
      have ha : ASub.arrow ≫ a = g ≫ (ηM.app Z).f n ≫ toI := by
        simp [a]
      have hι : c.ι.app j = (η.app Z).f n ≫ (e.inv.app Base).f n ≫ c.ι.app (Order.succ j) :=
        congrArg (fun q => q.f n) (iterationCocone_ι_app_eq η j hj Base)
      rw [hι, reassoc_of% ha]
      simp [leg, η, composeFunctorialInclusions, α, ← hfactor]
      rfl
    constructor
    intro f g sq
    obtain ⟨l, hl⟩ := hSextend f
    exact CommSq.HasLift.mk' ⟨l, hl, (isZero_zero C).eq_of_tgt _ _⟩
  apply (injective_iff_rlp_monomorphisms_zero _).2
  rw [← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  exact hgen

/-- **Stacks Project, Tag 079P**, relative to Tag 079N.  Given a functorial
injective enlargement of cochain complexes (the conclusion of Tag 079N),
functorial K-injective resolutions exist in a Grothendieck abelian category:
every complex `M` admits, functorially in `M`, a termwise monomorphic
quasi-isomorphism into a K-injective complex with injective terms.

This takes the Tag 079N datum as an explicit hypothesis.  It is no longer the
tagged form of Tag 079P: the datum is now discharged unconditionally by
`Stacks.Injectives.FunctorialEnlargement.exists_functorialInjectiveResolution`, and
`Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective`
carries the tag.  This statement is kept because it is the form the
induction is actually proved in. -/
theorem exists_functorial_quasiIso_isKInjective_of_functorialInjectiveResolution
    (NR : FunctorialInjectiveResolution C) :
    Nonempty (FunctorialKInjectiveResolution C) := by
  let κ₀ := Stacks.Injectives.acyclicComplexSizeBound (C := C)
  obtain ⟨lam, I, K, hK, hcover⟩ :=
    exists_small_boundedAbove_acyclic_representatives (C := C) κ₀
  let U := separator C
  have hU : IsSeparator U := isSeparator_separator C
  obtain ⟨κ, hκreg, hlam, hI, hUcard⟩ := exists_large_regular_cardinal
    (C := C) lam I U
  let F := killMapsObjectFunctor C I K
  let ηF := killMapsObjectInclusion C I K
  let N := functorialInjectiveStep C NR
  let ηN := functorialInjectiveStepInclusion C NR
  let : Fact κ.IsRegular := ⟨hκreg⟩
  have hκne : Nonempty κ.ord.ToType := by simpa using hκreg.ne_zero
  let : Nonempty κ.ord.ToType := hκne
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  let : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκreg.aleph0_le
  let : IsCardinalFiltered κ.ord.ToType κ := inferInstance
  let T := iterateCompositeFunctor F N ηF ηN κ
  let ηT := iterateCompositeFunctorInclusion F N ηF ηN κ
  have hFmono (X : CochainComplex C ℤ) : Mono ((ηF.app X)) :=
    killMapsObjectInclusion_mono_complex C I K X
  have hNmono (X : CochainComplex C ℤ) : Mono ((ηN.app X)) :=
    functorialInjectiveStepInclusion_mono_complex C NR X
  have hNqi (X : CochainComplex C ℤ) : QuasiIso ((ηN.app X)) :=
    functorialInjectiveStepInclusion_quasiIso C NR X
  have hFqi (X : CochainComplex C ℤ) : QuasiIso ((ηF.app X)) :=
    killMapsObjectInclusion_quasiIso C I K (fun i => (hK i).1) X
  have hTqi (X : CochainComplex C ℤ) : QuasiIso ((ηT.app X)) := by
    simpa [ηT] using iterateCompositeFunctorInclusion_quasiIso C F N ηF ηN hFqi hNqi κ X
  have hTmono (X : CochainComplex C ℤ) : Mono ((ηT.app X)) := by
    simpa [ηT] using iterateCompositeFunctorInclusion_mono F N ηF ηN hFmono hNmono κ X
  have hterm (X : CochainComplex C ℤ) (n : ℤ) : Injective ((T.obj X).X n) :=
    iterateCompositeFunctor_term_injective C NR F ηF hFmono κ U hU hUcard X n
  have hvanish (X : CochainComplex C ℤ) :
      ∀ (M : CochainComplex C ℤ), M.Acyclic →
        (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (M.X n)) →
        (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (M.X n))) ≤ κ₀) →
        ∀ f : M ⟶ T.obj X, Nonempty (Homotopy f 0) := by
    intro M hM hMtop hMsize f
    obtain ⟨i, ⟨e⟩⟩ := hcover M hM hMtop hMsize
    let g : K i ⟶ T.obj X := e.hom ≫ f
    have hKi : HasCardinalLT (Subobject (K i)) κ :=
      subobject_hasCardinalLT_of_bounded_cardinality C (K i) κ lam (hK i).2 hlam
    obtain ⟨j, g₀, hg₀⟩ := factor_through_iterateCompositeFunctor C F N ηF ηN
      hFmono hNmono κ (K i) X hKi g
    let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans
      (composeFunctorialInclusions F N ηF ηN)
    let Tj := S.iterationFunctor κ.ord.ToType
    have hj : ¬ IsMax j := not_isMax j
    let leg := ((S.iterationCocone κ.ord.ToType).ι.app j).app X
    obtain ⟨hkill⟩ : homotopic C (ComplexShape.up ℤ) (g₀ ≫ ηF.app ((Tj.obj j).obj X)) 0 :=
      killMapsObjectInclusion_kills_map C I K ((Tj.obj j).obj X) i g₀
    have hkill' : homotopic C (ComplexShape.up ℤ) (g₀ ≫ leg) 0 := by
      have hpost := hkill.compRight (ηN.app (F.obj ((Tj.obj j).obj X)) ≫
        (S.iterationFunctorObjSuccIso j hj).inv.app X ≫
        ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X)
      refine ⟨(Homotopy.ofEq ?_).trans (by simpa only [zero_comp, Category.assoc] using hpost)⟩
      rw [show leg = _ from iterationCocone_ι_app_eq (composeFunctorialInclusions F N ηF ηN) j hj X]
      simp [composeFunctorialInclusions]
      rfl
    have hfactor : g = g₀ ≫ leg := hg₀
    have hgfzero : homotopic C (ComplexShape.up ℤ) g 0 := by
      rw [hfactor]
      exact hkill'
    have he : f = e.inv ≫ g := by simp [g]
    rw [he]
    obtain ⟨hgfzero⟩ := hgfzero
    exact ⟨by simpa [Category.assoc] using hgfzero.compLeft e.inv⟩
  exact ⟨{
    functor := T
    inclusion := ηT
    quasiIso := hTqi
    mono_f X n := by
      have := hTmono X
      infer_instance
    injective := hterm
    isKInjective X :=
      Stacks.Injectives.isKInjective_of_small_boundedAbove_acyclic (T.obj X) (hterm X)
        (hvanish X) }⟩

end Stacks.Injectives.KInjectiveResolution
