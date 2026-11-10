module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorZariskiGluing

/-!
# Representability of the Hilbert functor from an open covering by representable subfunctors

Let `X` be a scheme over `S` and `d` a natural number. This file proves the gluing criterion of
Stacks 01JJ for the degree-`d` Hilbert functor `Hilb^d_{X/S}`, in the form the proofs of Stacks
0B99 and 0B9A use it: if subfunctors `F i ⊆ Hilb^d_{X/S}` are open, representable, and cover
`Hilb^d_{X/S}` at points with values in fields, then `Hilb^d_{X/S}` is representable.

## Main definitions

* `Stacks.Hilbert.yonedaToTotal`: for a scheme `H` representing a subfunctor of the Hilbert
  functor, the induced morphism from the functor of points of `H` to the Hilbert functor on all
  schemes, `Stacks.Hilbert.hilbertTotalPresheaf`.
* `Stacks.Hilbert.classifyingMap`: the morphism from the open `V ⊆ T` where the base changes of a
  family over `T` lie in an open subfunctor, to its representing scheme.
* `Stacks.Hilbert.representsOfTotal`: a representing scheme of `hilbertTotalPresheaf X d`
  represents the degree-`d` Hilbert functor of `X`.

## Main results

* `Stacks.Hilbert.isPullback_yonedaToTotal` and
  `Stacks.Hilbert.isOpenImmersion_presheaf_yonedaToTotal`: an open representable subfunctor
  gives a relatively representable open immersion into `hilbertTotalPresheaf X d`.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor`: **the
  gluing criterion, Stacks 01JJ, for the Hilbert functor.**

## Implementation notes

*Reduction to Mathlib's 01JJ.* Mathlib proves 01JJ as
`AlgebraicGeometry.Scheme.LocalRepresentability`, for Zariski sheaves on the category of all
schemes rather than on schemes over `S`. The Hilbert functor is transported there as
`Stacks.Hilbert.hilbertTotalPresheaf`, `T ↦ Σ (t : T ⟶ S), Hilb^d_{X/S}(T, t)`, a Zariski sheaf
by `Stacks.Hilbert.isSheaf_hilbertTotalPresheaf`, and a representation of it is transported back
by `Stacks.Hilbert.representsOfTotal`: maps `T ⟶ H` of `S`-schemes are exactly the maps of
schemes `T ⟶ H` whose classified element has structure morphism `T ⟶ S`.

*The open immersions.* For a family `Z` over a scheme `T` and the open `V ⊆ T` given by openness
of `F`, the square formed by `V ⟶ T` and the morphism classifying `Z|_V` is cartesian
(`Stacks.Hilbert.isPullback_yonedaToTotal`), which is condition (2)(b) of Stacks 01JJ in the form
`AlgebraicGeometry.IsOpenImmersion.presheaf` of Mathlib.

*The covering condition.* Mathlib asks that the induced morphism from the coproduct of the
functors of points be locally surjective. A point `y` of `T` gives the point
`Spec κ(y) ⟶ T` with values in a field, where some `F i` contains the base change of `Z` by
hypothesis; openness of `F i` then puts `y` in the corresponding open, and these opens form a
Zariski covering on whose members `Z` lifts.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) {d : ℕ}

section Subfunctor

variable {X} {F : Subfunctor (hilbertFunctorOfRank X d)} {H : Over S}
  (R : F.toFunctor.RepresentableBy H)

/-- The family classified by a morphism to a representing scheme of a subfunctor depends only on
the underlying morphism of schemes. -/
theorem totalFamily_mk_homEquiv_eq {T : Scheme.{u}} {t t' : T ⟶ S} (φ : Over.mk t ⟶ H)
    (φ' : Over.mk t' ⟶ H) (h : φ.left = φ'.left) :
    (⟨t, (R.homEquiv φ).1⟩ : TotalFamily X d T) = ⟨t', (R.homEquiv φ').1⟩ := by
  obtain rfl : t = t' := by
    have h₁ := Over.w φ
    have h₂ := Over.w φ'
    simp only [Over.mk_hom] at h₁ h₂
    rw [← h₁, ← h₂, h]
  rw [Over.OverMorphism.ext h]

/-- The underlying family of the family classified by a composite. -/
theorem homEquiv_comp_val {T' T : Over S} (g : T' ⟶ T) (φ : T ⟶ H) :
    (R.homEquiv (g ≫ φ)).1 = baseChange X g (R.homEquiv φ).1 := by
  rw [R.homEquiv_comp]
  rfl

/-- The morphism from the functor of points of a representing scheme of a subfunctor of the
Hilbert functor to the Hilbert functor on all schemes. -/
def yonedaToTotal : yoneda.obj H.left ⟶ hilbertTotalPresheaf X d where
  app T := ↾fun a ↦ ⟨a ≫ H.hom, (R.homEquiv (Over.homMk a rfl : Over.mk (a ≫ H.hom) ⟶ H)).1⟩
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    intro a
    refine (totalFamily_mk_homEquiv_eq R
      (Over.homMk (g.unop ≫ a) rfl : Over.mk ((g.unop ≫ a) ≫ H.hom) ⟶ H)
      ((Over.homMk g.unop rfl : Over.mk (g.unop ≫ a ≫ H.hom) ⟶ Over.mk (a ≫ H.hom)) ≫
        (Over.homMk a rfl : Over.mk (a ≫ H.hom) ⟶ H)) (by simp)).trans ?_
    rw [homEquiv_comp_val]
    rfl

/-- The value of `yonedaToTotal` at a morphism `a`. -/
theorem yonedaToTotal_app {T : Scheme.{u}} (a : T ⟶ H.left) :
    (yonedaToTotal R).app (op T) a =
      ⟨a ≫ H.hom, (R.homEquiv (Over.homMk a rfl : Over.mk (a ≫ H.hom) ⟶ H)).1⟩ :=
  rfl

/-- `yonedaToTotal` sends the morphism classifying a family to that family. -/
theorem yonedaToTotal_app_homEquiv_symm {T : Over S} (Z : F.toFunctor.obj (op T)) :
    (yonedaToTotal R).app (op T.left) (R.homEquiv.symm Z).left = ⟨T.hom, Z.1⟩ := by
  rw [yonedaToTotal_app]
  refine (totalFamily_mk_homEquiv_eq R
    (Over.homMk (R.homEquiv.symm Z).left rfl :
      Over.mk ((R.homEquiv.symm Z).left ≫ H.hom) ⟶ H)
    (R.homEquiv.symm Z : Over.mk T.hom ⟶ H) rfl).trans ?_
  rw [Equiv.apply_symm_apply]

variable {T : Scheme.{u}} {t : T ⟶ S} {Z : HilbertFamily X (Over.mk t) d} {V : T.Opens}
  (hV : ∀ (T' : Over S) (g : T' ⟶ Over.mk t), baseChange X g Z ∈ F.obj (op T') ↔
    Set.range g.left ⊆ (V : Set T))

include hV in
/-- The restriction of `Z` to an open `V` such that `F` consists of the base changes of `Z` along
morphisms into `V` lies in `F`. -/
theorem baseChange_ι_mem :
    baseChange X (Over.homMk V.ι rfl : Over.mk (V.ι ≫ t) ⟶ Over.mk t) Z ∈
      F.obj (op (Over.mk (V.ι ≫ t))) :=
  (hV _ _).mpr (by simp)

/-- The morphism from the open `V` of `T` to the representing scheme `H` of `F` classifying the
restriction of `Z` to `V`. -/
def classifyingMap : Over.mk (V.ι ≫ t) ⟶ H :=
  R.homEquiv.symm ⟨_, baseChange_ι_mem hV⟩

/-- The family classified by `classifyingMap` is the restriction of `Z` to `V`. -/
theorem homEquiv_classifyingMap_val :
    (R.homEquiv (classifyingMap R hV)).1 =
      baseChange X (Over.homMk V.ι rfl : Over.mk (V.ι ≫ t) ⟶ Over.mk t) Z :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The morphism `classifyingMap` classifies the restriction of `Z` to `V`. -/
theorem yonedaToTotal_app_classifyingMap :
    (yonedaToTotal R).app (op V) (classifyingMap R hV).left =
      (hilbertTotalPresheaf X d).map V.ι.op ⟨t, Z⟩ :=
  yonedaToTotal_app_homEquiv_symm R _

/-- **The pullback square of Stacks 01JJ (2)(b).** For a family `Z` over a scheme `T` and the open
`V ⊆ T` where its base changes lie in `F`, the square formed by `V ⟶ T`, the classifying map
`V ⟶ H` and the two maps to the Hilbert functor is cartesian. -/
theorem isPullback_yonedaToTotal :
    IsPullback (yoneda.map (classifyingMap R hV).left) (yoneda.map V.ι) (yonedaToTotal R)
      (yonedaEquiv.symm (⟨t, Z⟩ : TotalFamily X d T)) := by
  have hw : yoneda.map (classifyingMap R hV).left ≫ yonedaToTotal R =
      yoneda.map V.ι ≫ yonedaEquiv.symm (⟨t, Z⟩ : TotalFamily X d T) := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    exact yonedaToTotal_app_classifyingMap R hV
  refine IsPullback.of_forall_isPullback_app fun W ↦ (Types.isPullback_iff _ _ _ _).mpr
    ⟨by simpa using NatTrans.congr_app hw W, fun _ _ ⟨_, h⟩ ↦ (cancel_mono V.ι).mp h, ?_⟩
  intro (β : W.unop ⟶ H.left) (α : W.unop ⟶ T) h
  change (⟨β ≫ H.hom, (R.homEquiv (Over.homMk β rfl : Over.mk (β ≫ H.hom) ⟶ H)).1⟩ :
    TotalFamily X d W.unop) =
      ⟨α ≫ t, baseChange X (Over.homMk α rfl : Over.mk (α ≫ t) ⟶ Over.mk t) Z⟩ at h
  have hβ : β ≫ H.hom = α ≫ t := congrArg Sigma.fst h
  let β' : Over.mk (α ≫ t) ⟶ H := Over.homMk β hβ
  have h₁ : (R.homEquiv β').1 =
      baseChange X (Over.homMk α rfl : Over.mk (α ≫ t) ⟶ Over.mk t) Z := by
    rw [totalFamily_mk_homEquiv_eq R (Over.homMk β rfl : Over.mk (β ≫ H.hom) ⟶ H) β' rfl] at h
    exact eq_of_heq (Sigma.mk.inj h).2
  have hmem := (R.homEquiv β').2
  rw [h₁] at hmem
  have hrange : Set.range α ⊆ Set.range V.ι := by simpa using (hV _ _).mp hmem
  let c : W.unop ⟶ V := IsOpenImmersion.lift V.ι α hrange
  have hc : c ≫ V.ι = α := IsOpenImmersion.lift_fac _ _ _
  let cO : Over.mk (α ≫ t) ⟶ Over.mk (V.ι ≫ t) :=
    Over.homMk c (show c ≫ V.ι ≫ t = α ≫ t by rw [← Category.assoc, hc])
  have hcO : cO ≫ classifyingMap R hV = β' := by
    refine R.homEquiv.injective (Subtype.ext ?_)
    rw [homEquiv_comp_val, homEquiv_classifyingMap_val, h₁, ← baseChange_comp]
    exact baseChange_congr X (by simp [cO, hc]) Z
  exact ⟨c, congrArg CommaMorphism.left hcO, hc⟩

omit hV in
/-- **Condition (2)(b) of Stacks 01JJ, in Mathlib's form.** The morphism from the functor of
points of a representing scheme of an open subfunctor of the Hilbert functor is a relatively
representable open immersion. -/
theorem isOpenImmersion_presheaf_yonedaToTotal (hF : IsOpenHilbertSubfunctor F) :
    IsOpenImmersion.presheaf (yonedaToTotal R) := by
  refine MorphismProperty.relative.of_exists fun T g ↦ ?_
  obtain ⟨⟨t, Z⟩, rfl⟩ := yonedaEquiv.symm.surjective g
  obtain ⟨V, hV⟩ := hF (Over.mk t) Z
  exact ⟨V, yoneda.map (classifyingMap R hV).left, V.ι, isPullback_yonedaToTotal R hV,
    inferInstance⟩

end Subfunctor

/-! ### From the presheaf on all schemes back to the Hilbert functor -/

section Total

variable {X} {H₀ : Scheme.{u}} (rep : (hilbertTotalPresheaf X d).RepresentableBy H₀)

/-- The element classified by a morphism to a representing scheme of the Hilbert functor on all
schemes is the base change of the universal element. -/
theorem homEquiv_eq_mk {T : Scheme.{u}} (m : T ⟶ H₀) :
    rep.homEquiv m = ⟨m ≫ (rep.homEquiv (𝟙 H₀)).1, baseChange X
      (Over.homMk m rfl : Over.mk (m ≫ (rep.homEquiv (𝟙 H₀)).1) ⟶
        Over.mk (rep.homEquiv (𝟙 H₀)).1) (rep.homEquiv (𝟙 H₀)).2⟩ := by
  conv_lhs => rw [← Category.comp_id m, rep.homEquiv_comp]
  rfl

/-- The structure morphism of the element classified by `m` is `m` followed by the structure
morphism of the universal element. -/
theorem homEquiv_fst {T : Scheme.{u}} (m : T ⟶ H₀) :
    (rep.homEquiv m).1 = m ≫ (rep.homEquiv (𝟙 H₀)).1 := by
  rw [homEquiv_eq_mk rep m]

/-- **From a representation of `hilbertTotalPresheaf` to one of the Hilbert functor**, in terms
of a universal element `⟨p, U⟩`: the scheme `H₀`, viewed over `S` through `p`, represents the
degree-`d` Hilbert functor of `X`. -/
def representsOfTotalOfEq (p : H₀ ⟶ S) (U : HilbertFamily X (Over.mk p) d)
    (hrep : ∀ {T : Scheme.{u}} (m : T ⟶ H₀),
      rep.homEquiv m = ⟨m ≫ p, baseChange X (Over.homMk m rfl : Over.mk (m ≫ p) ⟶ Over.mk p) U⟩) :
    RepresentsHilbertFunctorOfRank X (Over.mk p) d where
  family {T} :=
    { toFun a := baseChange X a U
      invFun Z := (Over.homMk (rep.homEquiv.symm ⟨T.hom, Z⟩) (by
          have h := rep.homEquiv.apply_symm_apply (⟨T.hom, Z⟩ : TotalFamily X d T.left)
          rw [hrep] at h
          exact congrArg Sigma.fst h) : T ⟶ Over.mk p)
      left_inv a := by
        refine Over.OverMorphism.ext (rep.homEquiv.symm_apply_eq.mpr ?_)
        rw [hrep]
        exact totalFamily_mk_baseChange_eq X (a : Over.mk T.hom ⟶ Over.mk p)
          (Over.homMk a.left rfl : Over.mk (a.left ≫ p) ⟶ Over.mk p) rfl U
      right_inv Z := by
        have h := rep.homEquiv.apply_symm_apply (⟨T.hom, Z⟩ : TotalFamily X d T.left)
        rw [hrep] at h
        have h' : rep.homEquiv.symm ⟨T.hom, Z⟩ ≫ p = T.hom := congrArg Sigma.fst h
        rw [totalFamily_mk_baseChange_eq X
          (Over.homMk (rep.homEquiv.symm ⟨T.hom, Z⟩) rfl :
            Over.mk (rep.homEquiv.symm ⟨T.hom, Z⟩ ≫ p) ⟶ Over.mk p)
          (Over.homMk (rep.homEquiv.symm ⟨T.hom, Z⟩) h' : Over.mk T.hom ⟶ Over.mk p) rfl] at h
        exact eq_of_heq (Sigma.mk.inj h).2 }
  naturality g f := by
    change (baseChange X (g ≫ f) U).ideal = (baseChange X f U).ideal.comap (familyBaseChangeMap X g)
    rw [baseChange_comp]
    rfl

/-- **From a representation of `hilbertTotalPresheaf` to one of the Hilbert functor.** A scheme
representing the Hilbert functor on all schemes, viewed over `S` through the structure morphism
of its universal element, represents the degree-`d` Hilbert functor of `X`. -/
def representsOfTotal : Σ H : Over S, RepresentsHilbertFunctorOfRank X H d :=
  ⟨_, representsOfTotalOfEq rep _ _ (homEquiv_eq_mk rep)⟩

end Total

/-! ### The gluing criterion -/

/-- **Stacks Project, Tag 01JJ, for the Hilbert functor.** Let `F i` be subfunctors of the
degree-`d` Hilbert functor of `X` over `S` which are open (condition (2)(b)) and representable
(condition (2)(a)), and which cover it at points with values in fields (condition (2)(c)). Then
the degree-`d` Hilbert functor of `X` is representable.

That the Hilbert functor is a Zariski sheaf (condition (1)) is not a hypothesis: it is
`Stacks.Hilbert.isSheaf_hilbertTotalPresheaf`. The general criterion is Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`, which carries the tag; this is
its instance for the Hilbert functor of schemes over `S`, so it carries none. -/
theorem exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor
    {S : Scheme.{u}} (X : Over S) (d : ℕ) {ι : Type u}
    (F : ι → Subfunctor (hilbertFunctorOfRank X d))
    (hopen : ∀ i, IsOpenHilbertSubfunctor (F i))
    (hrep : ∀ i, ∃ H : Over S, Nonempty ((F i).toFunctor.RepresentableBy H))
    (hcov : ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S)
      (Z : HilbertFamily X (Over.mk g) d), ∃ i, Z ∈ (F i).obj (Opposite.op (Over.mk g))) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  choose H hH using hrep
  let R (i : ι) := (hH i).some
  let G : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨hilbertTotalPresheaf X d, (isSheaf_iff_isSheaf_of_type _ _).mpr
      (isSheaf_hilbertTotalPresheaf X d)⟩
  let f (i : ι) : yoneda.obj (H i).left ⟶ G.obj := yonedaToTotal (R i)
  have hf (i : ι) : IsOpenImmersion.presheaf (f i) :=
    isOpenImmersion_presheaf_yonedaToTotal (R i) (hopen i)
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    rintro T ⟨t, Z⟩
    choose V hV using fun i ↦ hopen i (Over.mk t) Z
    have hpt (y : T) : ∃ i, y ∈ V i := by
      obtain ⟨i, hi⟩ := hcov (T.residueField y) (T.fromSpecResidueField y ≫ t)
        (baseChange X (Over.homMk (T.fromSpecResidueField y) rfl :
          Over.mk (T.fromSpecResidueField y ≫ t) ⟶ Over.mk t) Z)
      have hy : y ∈ Set.range (T.fromSpecResidueField y) := by
        simp [Scheme.range_fromSpecResidueField]
      exact ⟨i, (hV i _ _).mp hi hy⟩
    choose idx hidx using hpt
    have key (y : T) : Presheaf.imageSieve (Sigma.desc f) (⟨t, Z⟩ : TotalFamily X d T)
        (V (idx y)).ι := by
      refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (H i).left) (idx y)).app _
        (classifyingMap (R (idx y)) (hV (idx y))).left, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc]
      exact yonedaToTotal_app_classifyingMap (R (idx y)) (hV (idx y))
    let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T (fun y ↦ (V (idx y)).toScheme)
      (fun y ↦ (V (idx y)).ι) fun y ↦ ⟨y, ⟨y, hidx y⟩, rfl⟩
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rintro W g ⟨Y, h, k, ⟨y⟩, rfl⟩
    exact Sieve.downward_closed _ (key y) h
  exact ⟨representsOfTotal (Scheme.LocalRepresentability.representableBy (F := G) hf)⟩

end Stacks.Hilbert

end
