module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighbourhoodOpenCopy
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# A family of open copies of an étale neighbourhood inside a base change

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S` and let
`x₁, …, xₙ` be distinct points of `|X|` with a common image `y` in `|Y|` at which `f` is étale.
Then there is a *single* étale morphism `g : U ⟶ Y` with a point `u` of `|U|` over `y` such
that the base change `U ×_Y X` contains `n` open and closed subspaces `V₁, …, Vₙ`, each mapping
**isomorphically** onto `U`, the `i`-th carrying a point lying over `u` and over `xᵢ`, and no
two of which meet over `u`.

## Main results

* `AlgebraicGeometry.Space.exists_etale_neighbourhood_forall_pointsMap_eq`: finitely many
  pointed étale morphisms to `Y` over one point of `|Y|` are refined by a single one.
* `AlgebraicGeometry.Space.exists_etale_neighbourhood_isIso_clopenSubspace_family_of_isEtaleAt`
  is the theorem described above.
* `AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_of_isEtaleAt`: for a single
  point, the two-piece decomposition of `U ×_Y X` in the shape of [Stacks, Tag 0ADU] with the
  distinguished piece an **isomorphism** onto `U` rather than merely finite over it.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 04HH](https://stacks.math.columbia.edu/tag/04HH)
* [Stacks Project, Tag 04HL](https://stacks.math.columbia.edu/tag/04HL)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A common refinement of finitely many pointed étale morphisms.**

Let `Y` be an algebraic space over `S`, let `y` be a point of `|Y|`, and let `hᵢ : Wᵢ ⟶ Y` be
finitely many étale morphisms with points `wᵢ` of `|Wᵢ|` over `y`. Then there are an étale
morphism `g : U ⟶ Y` and a point `u` of `|U|` over `y` which maps to each `wᵢ` under a morphism
`pᵢ : U ⟶ Wᵢ` over `Y`. -/
theorem exists_etale_neighbourhood_forall_pointsMap_eq
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y) :
    ∀ {n : ℕ} (W : Fin n → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : ∀ i, IsAlgebraicSpace B S hS (W i)) (h : ∀ i, W i ⟶ Y)
      (_ : ∀ i, IsEtale B S hS (h i)) (w : ∀ i, points B S hS (W i))
      (_ : ∀ i, pointsMap B S hS (W i) (h i) (w i) = y),
      ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
        (u : points B S hS U) (p : ∀ i, U ⟶ W i),
        IsEtale B S hS g ∧
        pointsMap B S hS U g u = y ∧
        (∀ i, p i ≫ h i = g) ∧
        (∀ i, pointsMap B S hS U (p i) u = w i) := by
  intro n
  induction n with
  | zero =>
    intro W _ h _ w _
    refine ⟨Y, hY, 𝟙 Y, y, fun i => i.elim0, fun _ _ hφ => by simpa using hφ, ?_,
      fun i => i.elim0, fun i => i.elim0⟩
    simp
  | succ n ih =>
    intro W hW h hh w hwy
    obtain ⟨U₀, hU₀, g₀, u₀, p₀, hg₀e, hg₀y, hp₀c, hp₀u⟩ :=
      ih (fun j => W j.castSucc) (fun j => hW j.castSucc) (fun j => h j.castSucc)
        (fun j => hh j.castSucc) (fun j => w j.castSucc) (fun j => hwy j.castSucc)
    have hP : IsAlgebraicSpace B S hS (pullback (h (Fin.last n)) g₀) :=
      _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (h (Fin.last n)) g₀
        (hW (Fin.last n)) hU₀ hY
    have hsnd : IsEtale B S hS (pullback.snd (h (Fin.last n)) g₀) :=
      isEtale_pullback_snd B S hS hU₀ hY (hW (Fin.last n)) (h (Fin.last n)) g₀ (hh (Fin.last n))
    let Wl : AlgebraicSpaces B S hS := ⟨W (Fin.last n), hW (Fin.last n)⟩
    let Yb : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Ub : AlgebraicSpaces B S hS := ⟨U₀, hU₀⟩
    let hlb : Wl ⟶ Yb := ObjectProperty.homMk (h (Fin.last n))
    let g₀b : Ub ⟶ Yb := ObjectProperty.homMk g₀
    have hcart : IsPullback
        (ObjectProperty.homMk (pullback.fst hlb.hom g₀b.hom) :
          AlgebraicSpaces.fiberProduct B S hS hlb g₀b ⟶ Wl)
        (ObjectProperty.homMk (pullback.snd hlb.hom g₀b.hom) :
          AlgebraicSpaces.fiberProduct B S hS hlb g₀b ⟶ Ub) hlb g₀b :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS hlb g₀b
    obtain ⟨u, hu₁, hu₂⟩ :=
      exists_point_of_isPullback B S hS hcart (w (Fin.last n)) u₀
        ((hwy (Fin.last n)).trans hg₀y.symm)
    change points B S hS (pullback (h (Fin.last n)) g₀) at u
    change pointsMap B S hS (pullback (h (Fin.last n)) g₀)
      (pullback.fst (h (Fin.last n)) g₀) u = w (Fin.last n) at hu₁
    change pointsMap B S hS (pullback (h (Fin.last n)) g₀)
      (pullback.snd (h (Fin.last n)) g₀) u = u₀ at hu₂
    refine ⟨pullback (h (Fin.last n)) g₀, hP, pullback.snd (h (Fin.last n)) g₀ ≫ g₀, u,
      Fin.lastCases (motive := fun i => pullback (h (Fin.last n)) g₀ ⟶ W i)
        (pullback.fst (h (Fin.last n)) g₀)
        (fun j => pullback.snd (h (Fin.last n)) g₀ ≫ p₀ j),
      isEtale_comp B S hS hsnd hg₀e, ?_, ?_, ?_⟩
    · rw [pointsMap_comp_apply, hu₂, hg₀y]
    · refine Fin.lastCases ?_ fun j => ?_
      · rw [Fin.lastCases_last]
        exact pullback.condition
      · rw [Fin.lastCases_castSucc, Category.assoc, hp₀c j]
    · refine Fin.lastCases ?_ fun j => ?_
      · rwa [Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, pointsMap_comp_apply, hu₂, hp₀u j]

/-- **An étale neighbourhood over which the base change has a family of open and closed copies
of itself, one through each of finitely many prescribed points.**

Let `f : X ⟶ Y` be a **separated** morphism of algebraic spaces over `S`, let `y` be a point of
`|Y|`, and let `x₁, …, xₙ` be **distinct** points of `|X|` over `y` at which `f` is étale. Then
there are an algebraic space `U` over `S`, an **étale** morphism `g : U ⟶ Y` and a point `u` of
`|U|` over `y`, together with **open and closed** subspaces `V₁, …, Vₙ` of `U ×_Y X` such that
each `Vᵢ ⟶ U` is an **isomorphism**, some point of `|Vᵢ|` lies over `x i` in `|X|` and over `u`
in `|U|`, and no point of `|U ×_Y X|` lying in two different copies lies over `u`. -/
theorem exists_etale_neighbourhood_isIso_clopenSubspace_family_of_isEtaleAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (y : points B S hS Y)
    {n : ℕ} (x : Fin n → points B S hS X) (hinj : Function.Injective x)
    (hxy : ∀ i, pointsMap B S hS X f (x i) = y)
    (hf : ∀ i, IsEtaleAt B S hS f (x i)) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (V : Fin n → Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u = y ∧
      (∀ i, IsOpenSubspace B S hS (V i)) ∧
      (∀ i, IsClosedSubspace B S hS (V i)) ∧
      (∀ i, IsIso ((V i).ι ≫ pullback.fst g f)) ∧
      (∀ i, ∃ v : points B S hS (V i).toFunctor,
        pointsMap B S hS (V i).toFunctor ((V i).ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS (V i).toFunctor ((V i).ι ≫ pullback.snd g f) v = x i) ∧
      (∀ i j, i ≠ j → ∀ z : points B S hS (pullback g f),
        z ∈ Set.range (pointsMap B S hS (V i).toFunctor (V i).ι) →
        z ∈ Set.range (pointsMap B S hS (V j).toFunctor (V j).ι) →
        pointsMap B S hS (pullback g f) (pullback.fst g f) z ≠ u) := by
  classical
  choose A hA a ha hAet using hf
  obtain ⟨U, hU, g, u, p, hge, hgy, hpc, hpu⟩ :=
    exists_etale_neighbourhood_forall_pointsMap_eq B S hS hY y
      (fun i => (A i).toFunctor) (fun i => (hA i).1) (fun i => (A i).ι ≫ f)
      (fun i => hAet i) a
      (fun i => by rw [pointsMap_comp_apply, ha i, hxy i])
  have htf : ∀ i, 𝟙 U ≫ g = (p i ≫ (A i).ι) ≫ f := fun i => by
    rw [Category.id_comp, Category.assoc, hpc i]
  have htu : ∀ i, pointsMap B S hS U (p i ≫ (A i).ι) u = x i := fun i => by
    rw [pointsMap_comp_apply, hpu i, ha i]
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g f hU hX hY
  have hsnd : IsEtale B S hS (pullback.snd g f) :=
    isEtale_pullback_snd B S hS hX hY hU g f hge
  have htet : ∀ i, IsEtale B S hS (p i ≫ (A i).ι) := fun i =>
    isEtale_comp B S hS
      (isEtale_of_isEtale_over B S hS hU (hA i).1 hY (p i) g ((A i).ι ≫ f) hge (hAet i) (hpc i))
      (isEtale_of_isOpenImmersion B S hS (hA i).2)
  have hΓfst : ∀ i, pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i) ≫ pullback.fst g f = 𝟙 U :=
    fun i => pullback.lift_fst _ _ _
  have hΓopen : ∀ i,
      IsOpenImmersion B S hS (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i)) := fun i =>
    isOpenImmersion_of_isEtale_of_mono B S hS _ hU hP
      (isEtale_of_isEtale_over B S hS hU hP hX _ (p i ≫ (A i).ι) (pullback.snd g f)
        (htet i) hsnd (pullback.lift_snd _ _ _))
      (mono_of_mono_fac (hΓfst i))
  have hΓclosed : ∀ i,
      IsClosedImmersion B S hS (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i)) := fun i =>
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst g f)
      (isSeparated_pullbackFst B S hS g hsep) _ (hΓfst i)
  have hiso : ∀ i, IsIso
      ((Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).ι ≫
        pullback.fst g f) := fun i =>
    isIso_range_ι_comp_pullbackFst_pullbackLift_id B S hS (htf i)
  have hpoint : ∀ i, ∃ v : points B S hS
      (Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).toFunctor,
      pointsMap B S hS
          (Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).toFunctor
          ((Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).ι ≫
            pullback.fst g f) v = u ∧
        pointsMap B S hS
          (Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).toFunctor
          ((Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).ι ≫
            pullback.snd g f) v = x i := fun i =>
    exists_point_range_pullbackLift_id B S hS (htf i) u (x i) (htu i)
  have himage : ∀ (i : Fin n) (z : points B S hS (pullback g f)),
      z ∈ Set.range (pointsMap B S hS
        (Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).toFunctor
        (Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).ι) →
      pointsMap B S hS (pullback g f) (pullback.fst g f) z = u →
      pointsMap B S hS (pullback g f) (pullback.snd g f) z = x i := by
    intro i z hz hzu
    obtain ⟨v, rfl⟩ := hz
    obtain ⟨v₀, hv₀fst, hv₀snd⟩ := hpoint i
    have := hiso i
    have hveq : v = v₀ :=
      pointsMap_injective_of_mono B S hS
        ((Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i))).ι ≫ pullback.fst g f)
        (by rw [pointsMap_comp_apply, hzu, hv₀fst])
    rw [← pointsMap_comp_apply, hveq, hv₀snd]
  refine ⟨U, hU, g, u,
    fun i => Subfunctor.range (pullback.lift (𝟙 U) (p i ≫ (A i).ι) (htf i)), hge, hgy,
    fun i => isOpenSubspace_subfunctorRange B S hS hU (hΓopen i),
    fun i => isClosedSubspace_range_of_isClosedImmersion B S hS _ hU (hΓclosed i),
    hiso, hpoint, fun i j hij z hzi hzj hzu =>
      hij (hinj ((himage i z hzi hzu).symm.trans (himage j z hzj hzu)))⟩

/-- **The conclusion of [Stacks, Tag 0ADU] with the distinguished piece an isomorphism onto the
étale neighbourhood.**

Let `f : X ⟶ Y` be a **separated** morphism of algebraic spaces over `S` which is étale at a
point `x` of `|X|`. Then there are an algebraic space `U` over `S`, an **étale** morphism
`g : U ⟶ Y` and a point `u` of `|U|` over the image of `x`, together with a decomposition of
`U ×_Y X` into two open-and-closed subspaces `W` and `V` — their join sheafifies to everything
and their meet is the sheafification of nothing — such that `V ⟶ U` is an **isomorphism** and
some point of `|V|` lies over `u` and over `x`. -/
theorem exists_etale_decomposition_isIso_part_of_isEtaleAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (hsep : IsSeparated B S hS f)
    (hf : IsEtaleAt B S hS f x) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (W V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u = pointsMap B S hS X f x ∧
      IsOpenSubspace B S hS W ∧
      IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧
      IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback g f)).sheafify (BigFppfOver.topology B S hS) ∧
      IsIso (V.ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x := by
  obtain ⟨U, hU, g, u, V, hge, hgu, hVo, hVc, hiso, hv⟩ :=
    exists_etale_neighbourhood_isIso_clopenSubspace_of_isEtaleAt B S hS hX hY f x hsep hf
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g f hU hX hY
  obtain ⟨T, hTdef⟩ : ∃ T : Set (points B S hS (pullback g f)),
      T = Set.range (pointsMap B S hS V.toFunctor V.ι) := ⟨_, rfl⟩
  have hTo : IsOpen T :=
    hTdef ▸ isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hVo.2
  have hTc : IsClosed T :=
    hTdef ▸ isClosed_range_pointsMap_of_isClosedImmersion B S hS hP V.ι hVc.2
  have hVeq : V = openSubspaceOfPoints B S hS (pullback g f) T := by
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openSubspaceOfPoints B S hS hP T hTo) ?_)
      (le_of_range_pointsMap_ι_subset B S hS hVo ?_) <;>
      rw [range_pointsMap_ι_openSubspaceOfPoints, hTdef]
  rw [hVeq] at hVo hVc hiso hv
  exact ⟨U, hU, g, u, openSubspaceOfPoints B S hS (pullback g f) Tᶜ,
    openSubspaceOfPoints B S hS (pullback g f) T, hge, hgu,
    isOpenSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl hTo.isClosed_compl,
    hVo, hVc, sheafify_sup_openSubspaceOfPoints_eq_top B S hS T hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS T, hiso, hv⟩

end AlgebraicGeometry.Space

end
