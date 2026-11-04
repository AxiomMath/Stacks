module

public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStack
import StacksCore.Tactic.EgaSgaAttribute

/-! # The pullback along a morphism of sites coming from a fully faithful functor

Let `(𝒞, J)` and `(𝒟, K)` be sites and let `u : 𝒞 ⥤ 𝒟` satisfy the assumptions of
Sites 00XU: `u` is cocontinuous, continuous and fully faithful, `𝒞` has fibre products and a
final object, and `u` commutes with them. Let `f : 𝒟 ⟶ 𝒞` be the associated morphism of sites.
Stacks 04WS says:

1. for every stack `𝒮` over `(𝒞, J)` the canonical functor `𝒮 ⟶ f_*f⁻¹𝒮` is an equivalence of
   stacks over `𝒞`;
2. for stacks `𝒮` and `𝒮₂` over `(𝒞, J)` the construction `f⁻¹` induces an equivalence of the
   morphism categories `Mor_{Stacks/𝒞}(𝒮, 𝒮₂) ≃ Mor_{Stacks/𝒟}(f⁻¹𝒮, f⁻¹𝒮₂)`.

Both are proved here, **modulo Stacks 02ZN**: the construction of the stackification of a fibred
category is not yet assembled in this tree, so — exactly as in
`StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor` (Stacks 0435),
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid` (Stacks 04Y2) and
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStack` (Stacks 04WJ) — the pullback
`f⁻¹𝒮` is taken *relative to a supplied stackification*: a stack `q : 𝒳 ⥤ 𝒟` and a 1-morphism
`G : u_p 𝒮 ⥤ 𝒳` of fibred categories over `𝒟` satisfying the two clauses `hmor` and `hobj` of
Stacks 02ZN. Once Stacks 02ZN is assembled it supplies that data and the two statements become
unconditional.

## Main definitions

* `CategoryTheory.Comma.pullbackUnitLoc`, the unit `ι : 𝒮 ⥤ u_p 𝒮`, `x ↦ (p(x), id, x)`;
* `CategoryTheory.Comma.pullbackUnitPush`, the same functor read as a 1-morphism
  `𝒮 ⥤ u^p(u_p 𝒮)` of fibred categories over `𝒞`;
* `CategoryTheory.Comma.pullbackStackCan`, the canonical 1-morphism `can : 𝒮 ⟶ f_*f⁻¹𝒮` of
  Stacks 04WS (1), namely the image of `G` under the functor `A` of Stacks 04WI;
* `CategoryTheory.Comma.postcompFibredMor`, post-composition on morphism categories.

## Main results

* `CategoryTheory.Comma.equivalenceOverPullbackStackCan`: **Stacks 04WS (1)**, the equivalence
  over `𝒞` exhibited by `can`, as data;
* `CategoryTheory.Comma.equivalenceFibredMorPullbackStack`: **Stacks 04WS (2)**, the equivalence
  of morphism categories;
* `CategoryTheory.Comma.equivalenceOverPullbackStackCanUniv` and
  `CategoryTheory.Comma.equivalenceFibredMorPullbackStackUniv`: Stacks 04WS (1) and (2) with
  independent universes for the base sites, the stack `𝒮` and its stackifications;
* `CategoryTheory.Comma.pullbackUnitLoc_full`, `CategoryTheory.Comma.pullbackUnitLoc_faithful` and
  `CategoryTheory.Comma.exists_iso_pullbackUnitLoc`: the unit is fully faithful and every object
  of `u_p 𝒮` over an object in the image of `u` is vertically isomorphic to one in its image —
  this is where full faithfulness of `u` enters;
* `CategoryTheory.Comma.faithful_of_fiber_faithful` and
  `CategoryTheory.Comma.full_of_fiber_full`: a 1-morphism of fibred categories which is fully
  faithful on every fibre is fully faithful, the analogue for fibred categories of Stacks 003Z (1).

## The proof

Clause (1) is Stacks 046N (`Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`): `𝒮` and
`f_*f⁻¹𝒮` are stacks (the latter by Stacks 04WC), so it suffices that `can` be fully faithful and
that every object of a fibre of `f_*f⁻¹𝒮` be locally in its essential image on fibres.

* *Local essential surjectivity* is `locallyEssSurjOnFibers_pullbackStackCan`. Clause (2) of
  Stacks 02ZN gives a `K`-covering sieve of `u(U)` along which the object comes from `u_p 𝒮`;
  **cocontinuity** of `u` pulls that sieve back to a `J`-covering sieve of `U`, and along its
  members the object of `u_p 𝒮` lies over an object in the image of `u` and therefore comes from
  `𝒮`, by `exists_iso_pullbackUnitLoc`.
* *Full faithfulness* is `fullyFaithful_pullbackStackCan`. By
  `faithful_of_fiber_faithful`/`full_of_fiber_full` it is enough to have it on each fibre, and the
  fibre of `f_*f⁻¹𝒮` over `U` is the fibre of `f⁻¹𝒮` over `u(U)`. There the statement is
  `bijective_morPresheafMap_unitFiber`: the presheaf `Mor(ι x, ι y)` on `𝒟/u(U)` restricts along
  `𝒞/U ⥤ 𝒟/u(U)` to `Mor(x, y)` on `𝒞/U` — because the unit is a *fully faithful* 1-morphism over
  `𝒞` into the pushforward of `u_p 𝒮` — so that restriction is a sheaf; the restriction of
  `Mor(G ι x, G ι y)` is a sheaf for the same reason; the map between them is locally bijective,
  being the restriction along a cocontinuous functor of a locally bijective map (clause (1) of
  Stacks 02ZN); and a locally bijective map of sheaves is an isomorphism.

Clause (2) is the composite of post-composition with the equivalence `𝒮₂ ⟶ f_*f⁻¹𝒮₂` of clause
(1) with the adjunction of Stacks 04WK at `𝒯 = f⁻¹𝒮₂`,

`Mor_{Stacks/𝒞}(𝒮, 𝒮₂) ≃ Mor_{Stacks/𝒞}(𝒮, f_*f⁻¹𝒮₂) ≃ Mor_{Stacks/𝒟}(f⁻¹𝒮, f⁻¹𝒮₂)`,

which is the source's own proof. As in Stacks 04WI and 04WK the conclusion is stated as the
equivalence itself, as data; its quasi-inverse is restriction, and `f⁻¹` is the direction the
source names.

## Implementation notes

*The hypotheses of Sites 00XU.* Assumptions (1)–(3) are `[u.IsCocontinuous J K]`,
`[u.IsContinuous J K]`, `[u.Full]` and `[u.Faithful]`. Assumptions (4) and (5) — fibre products in
`𝒞` commuting with `u`, and final objects `e_𝒞`, `e_𝒟` with `u(e_𝒞) = e_𝒟` — are spelled
`[Limits.HasFiniteLimits 𝒞]` and `[Limits.PreservesFiniteLimits u]`, which is the same thing: a
category with fibre products and a final object has all finite limits, and a functor preserving
both preserves all finite limits. That is also the spelling
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStack` (Stacks 04WJ) uses for the
hypotheses of Sites 00X6, and (4)+(5) are exactly those; 00XU adds (1) and (3), and both are used:
cocontinuity for the two transports of covering sieves, and full faithfulness of `u` for
`pullbackUnitLoc_full` and `exists_iso_pullbackUnitLoc`. The conclusion of 00XU that `u` defines a
morphism of sites `f : 𝒟 ⟶ 𝒞` is `Functor.isMorphismOfSites_of_preservesFiniteLimits`, and is what
the notations `f_*` and `f⁻¹` name; it is not repeated as a hypothesis.

*Universes.* The morphism presheaves of Stacks 02ZB force one hom universe on the base `𝒟`, on
`u_p 𝒮` and on `f⁻¹𝒮`, and `u_p 𝒮` has homs in `Type (max u₂ u₃ v₂ v₃)`; as in Stacks 04WJ and
04WK this is solved by `𝒟 : Type v` with `Category.{v} 𝒟` and `𝒮 : Type v` with `Category.{v} 𝒮`.
Stacks 046N adds one hom universe for the base, so `𝒞 : Type u₁` carries `Category.{v} 𝒞`; the
object universes of `𝒞` and of the two stackifications stay independent.

The declarations with the suffix `Univ` (or `_univ`) are the same constructions and results with
independent universes. The morphism presheaves of Stacks 02ZB force one hom universe on `u_p 𝒮`
and on `f⁻¹𝒮` only, and `u_p 𝒮` has homs in `Type (max u₂ u₃ vd vs)`, so there the
stackification carries `Category.{max u₂ u₃ vd vs}`. The morphism presheaves of `𝒮` and of
`f_*f⁻¹𝒮`, which then live in different universes, are compared through universe lifts
(`isIso_morPresheafMapULift_of_fullyFaithful`), so the hom universes `vc`, `vd`, `vs` of `𝒞`, `𝒟`
and `𝒮` and all object universes are independent. This is the form a big site, whose morphisms
are small while its objects are not, needs.

## References

* [Stacks 04WS](https://stacks.math.columbia.edu/tag/04WS);
* [Stacks 04WJ](https://stacks.math.columbia.edu/tag/04WJ);
* [Stacks 04WK](https://stacks.math.columbia.edu/tag/04WK);
* [Stacks 04WI](https://stacks.math.columbia.edu/tag/04WI);
* [Stacks 046N](https://stacks.math.columbia.edu/tag/046N);
* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN);
* [Sites 00XU](https://stacks.math.columbia.edu/tag/00XU).
-/
@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Composing a presheaf of types with the forgetful functor of `Type` changes nothing, so the
forgetful functor of `Type` preserves sheaves. -/
instance hasSheafCompose_forget_type {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget (Type v₂)) :=
  ⟨fun {_} hP => hP⟩

/-- Bijectivity of a component of a morphism of presheaves is transported along an equality of
objects. -/
lemma bijective_app_of_obj_eq {C : Type u₁} [Category.{v₁} C] {P Q : Cᵒᵖ ⥤ Type v₂} (φ : P ⟶ Q)
    {W₁ W₂ : C} (h : W₁ = W₂)
    (hb : Function.Bijective (φ.app (Opposite.op W₁))) :
    Function.Bijective (φ.app (Opposite.op W₂)) := by
  subst h
  exact hb

namespace Comma

section Unit

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- **The unit `ι : 𝒮 ⥤ u_p 𝒮`**, the composite of `CategoryTheory.Comma.pullbackUnit` with the
localization functor. On objects it is `x ↦ (p(x), id_{u(p(x))}, x)`. -/
noncomputable def pullbackUnitLoc : 𝒮 ⥤ pullbackLocalization p u :=
  pullbackUnit p u ⋙ (idBaseStronglyCartesian p u).Q

/-- The unit sends `x` to the localization of `pullbackUnit p u` applied to `x`. -/
lemma pullbackUnitLoc_obj (x : 𝒮) :
    (pullbackUnitLoc p u).obj x =
      (idBaseStronglyCartesian p u).Q.obj ((pullbackUnit p u).obj x) := rfl

/-- The unit sends `α` to the localization of `pullbackUnit p u` applied to `α`. -/
lemma pullbackUnitLoc_map {x y : 𝒮} (α : x ⟶ y) :
    (pullbackUnitLoc p u).map α =
      (idBaseStronglyCartesian p u).Q.map ((pullbackUnit p u).map α) := rfl

/-- The unit is a functor over `u`: it lifts `p ⋙ u` along the structure functor of `u_p 𝒮`. -/
lemma pullbackUnitLoc_comp_pullbackProj :
    pullbackUnitLoc p u ⋙ pullbackProj p u = p ⋙ u := by
  rw [pullbackUnitLoc, Functor.assoc, pullbackProj_fac]
  rfl

/-- A morphism of `u_pp 𝒮` **into** an object in the image of the unit is determined by its
`𝒮`-component: the commuting square defining a morphism of the comma category reads
`m_𝒟 = φ ≫ u(p(m_𝒮))` there, because the `𝒟`-component of `ι(y)` is an identity. -/
lemma hom_ext_toUnit {y : 𝒮} {W : Comma (𝟭 𝒟) (p ⋙ u)}
    (m m' : W ⟶ (pullbackUnit p u).obj y) (h : m.right = m'.right) : m = m' := by
  refine Comma.hom_ext _ _ ?_ h
  have hm : m.left = W.hom ≫ (p ⋙ u).map m.right := by
    have h0 : (𝟭 𝒟).map m.left ≫ ((pullbackUnit p u).obj y).hom =
      W.hom ≫ (p ⋙ u).map m.right := m.w
    simpa using h0
  have hm' : m'.left = W.hom ≫ (p ⋙ u).map m'.right := by
    have h0 : (𝟭 𝒟).map m'.left ≫ ((pullbackUnit p u).obj y).hom =
      W.hom ≫ (p ⋙ u).map m'.right := m'.w
    simpa using h0
  rw [hm, hm', h]

section

variable [p.IsFibered] [u.Full] [u.Faithful]

/-- **The splitting of an element of `R` with target in the image of the unit.** Let
`s : Z ⟶ ι(x)` be a morphism of `u_pp 𝒮` with identity `𝒟`-component and strongly cartesian
`𝒮`-component. Because `u` is fully faithful, the `𝒟`-component `Z.hom` of `Z` is the image under
`u` of a section `c` of `p(s_𝒮)`, and a cartesian lift `τ` of `c` produces a morphism
`t : ι(z') ⟶ Z`, again in `R`, with `t_𝒮 ≫ s_𝒮` an isomorphism. So `s_𝒮` is a split epimorphism of
`𝒮`, up to the further element `t` of `R`. -/
lemma exists_split_of_mem_toUnit {x : 𝒮} {Z : Comma (𝟭 𝒟) (p ⋙ u)}
    (s : Z ⟶ (pullbackUnit p u).obj x) (hs : idBaseStronglyCartesian p u s) :
    ∃ (z' : 𝒮) (t : (pullbackUnit p u).obj z' ⟶ Z),
      idBaseStronglyCartesian p u t ∧ IsIso (t.right ≫ s.right) := by
  obtain ⟨⟨h, hsleft⟩, hsc⟩ := hs
  -- `h : Z.left = u (p x)` and `s.left = eqToHom h`; `hsc : s.right` is strongly cartesian.
  have hw : s.left = Z.hom ≫ u.map (p.map s.right) := by
    have h0 : (𝟭 𝒟).map s.left ≫ ((pullbackUnit p u).obj x).hom =
      Z.hom ≫ (p ⋙ u).map s.right := s.w
    simpa using h0
  -- The section `c` of `p (s.right)`.
  have hfac : (eqToHom h.symm ≫ Z.hom) ≫ u.map (p.map s.right) = 𝟙 (u.obj (p.obj x)) := by
    rw [Category.assoc, ← hw, hsleft, eqToHom_trans, eqToHom_refl]
    rfl
  obtain ⟨c, hc⟩ := u.map_surjective (eqToHom h.symm ≫ Z.hom)
  have hcs : c ≫ p.map s.right = 𝟙 (p.obj x) := by
    apply u.map_injective
    rw [u.map_comp, hc, hfac, u.map_id]
  -- A cartesian lift of `c`.
  have hZr : p.obj Z.right = p.obj Z.right := rfl
  set z' : 𝒮 := Functor.IsPreFibered.pullbackObj hZr c with hz'
  set τ : z' ⟶ Z.right := Functor.IsPreFibered.pullbackMap hZr c with hτ
  have hτc : p.IsStronglyCartesian c τ := inferInstance
  have hz : p.obj z' = p.obj x := Functor.IsPreFibered.pullbackObj_proj hZr c
  have hτmap : p.map τ = eqToHom hz ≫ c ≫ eqToHom hZr := IsHomLift.fac' p c τ
  have hzl : ((pullbackUnit p u).obj z').left = Z.left := (congrArg u.obj hz).trans h.symm
  refine ⟨z', ⟨eqToHom hzl, τ, ?_⟩, ⟨⟨hzl, rfl⟩, ?_⟩, ?_⟩
  · rw [Functor.comp_map, hτmap]
    simp only [Functor.id_map, pullbackUnit_obj_hom, Functor.map_comp, eqToHom_refl,
      Category.comp_id, hc, eqToHom_map, ← Category.assoc, eqToHom_trans]
    simp
  · dsimp only [stronglyCartesianOver, pullbackUnit_obj_right, pullbackUnit_obj_left]
    rw [hτmap]
    exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom hz hZr c τ hτc
  · dsimp only
    have hsc' : p.IsStronglyCartesian (p.map s.right) s.right := hsc
    have hcomp : p.IsStronglyCartesian (c ≫ p.map s.right) (τ ≫ s.right) := by
      have := hτc
      have := hsc'
      exact Functor.IsStronglyCartesian.comp (p := p) (f := c) (g := p.map s.right)
        (φ := τ) (ψ := s.right)
    rw [hcs] at hcomp
    have := hcomp
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 (p.obj x)) (τ ≫ s.right)

variable [HasNonemptyFiniteLimits 𝒞]
  (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
    Limits.PreservesLimitsOfShape J u)

include hu

/-- **The unit is faithful** when `u` is fully faithful. Two morphisms of `𝒮` with the same image
in `u_p 𝒮` agree after composition with some element of `R`, hence after composition with the
isomorphism produced by `CategoryTheory.Comma.exists_split_of_mem_toUnit`. -/
lemma pullbackUnitLoc_faithful : (pullbackUnitLoc p u).Faithful := by
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  refine ⟨fun {x y} ξ ξ' hξ => ?_⟩
  rw [pullbackUnitLoc_map, pullbackUnitLoc_map,
    MorphismProperty.map_eq_iff_precomp (idBaseStronglyCartesian p u).Q
      (idBaseStronglyCartesian p u)] at hξ
  obtain ⟨Z, s, hs, hfac⟩ := hξ
  obtain ⟨z', t, ht, hiso⟩ := exists_split_of_mem_toUnit p u s hs
  have hr : s.right ≫ ξ = s.right ≫ ξ' := by
    simpa using congrArg CommaMorphism.right hfac
  have := hiso
  rw [← cancel_epi (t.right ≫ s.right), Category.assoc, Category.assoc, hr]

/-- **The unit is full** when `u` is fully faithful. A morphism `ι(x) ⟶ ι(y)` of `u_p 𝒮` is a
right fraction `Q(s)⁻¹ ≫ Q(f)` with `s : Z ⟶ ι(x)` in `R`; splitting `s` as in
`CategoryTheory.Comma.exists_split_of_mem_toUnit` and composing the numerator with the splitting
produces the morphism of `𝒮`. -/
lemma pullbackUnitLoc_full : (pullbackUnitLoc p u).Full := by
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  refine ⟨fun {x y} χ => ?_⟩
  obtain ⟨ϕ, hϕ⟩ := Localization.exists_rightFraction
    (idBaseStronglyCartesian p u).Q (idBaseStronglyCartesian p u) χ
  have hϕs : (idBaseStronglyCartesian p u).Q.map ϕ.s ≫ χ =
      (idBaseStronglyCartesian p u).Q.map ϕ.f := by
    rw [hϕ]
    exact MorphismProperty.RightFraction.map_s_comp_map ϕ _ _
  obtain ⟨z', t, ht, hiso⟩ := exists_split_of_mem_toUnit p u ϕ.s ϕ.hs
  have := hiso
  refine ⟨inv (t.right ≫ ϕ.s.right) ≫ t.right ≫ ϕ.f.right, ?_⟩
  have hQs : IsIso ((idBaseStronglyCartesian p u).Q.map ϕ.s) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ ϕ.hs
  rw [pullbackUnitLoc_map, ← cancel_epi ((idBaseStronglyCartesian p u).Q.map ϕ.s), hϕs,
    ← Functor.map_comp]
  rw [MorphismProperty.map_eq_iff_precomp (idBaseStronglyCartesian p u).Q
    (idBaseStronglyCartesian p u)]
  refine ⟨_, t, ht, ?_⟩
  refine hom_ext_toUnit p u _ _ ?_
  simp only [Comma.comp_right, pullbackUnit_map_right, ← Category.assoc]
  rw [IsIso.hom_inv_id, Category.id_comp]

omit [u.Faithful] in
/-- **Every object of `u_p 𝒮` lying over an object in the image of `u` is vertically isomorphic to
one in the image of the unit.** An object of `u_p 𝒮` over `u(V)` is the image of a triple
`Z = (u(V), φ : u(V) ⟶ u(p(w)), w)`; full faithfulness of `u` writes `φ = u(c)`, and a cartesian
lift `τ : z ⟶ w` of `c` makes `ι(τ)` a second strongly cartesian morphism over `φ` with the same
target `ι(w)` as the canonical morphism `c_Z : Z ⟶ ι(w)`, so their sources are isomorphic over the
identity. -/
lemma exists_iso_pullbackUnitLoc {V : 𝒞} (Y : pullbackLocalization p u)
    (hY : (pullbackProj p u).obj Y = u.obj V) :
    ∃ (z : 𝒮) (_ : p.obj z = V) (e : Y ≅ (pullbackUnitLoc p u).obj z),
      (pullbackProj p u).IsHomLift (𝟙 (u.obj V)) e.hom := by
  obtain ⟨Z, rfl⟩ : ∃ Z, (idBaseStronglyCartesian p u).Q.obj Z = Y :=
    ⟨_, (Localization.Construction.objEquiv (idBaseStronglyCartesian p u)).apply_symm_apply Y⟩
  have hZl : Z.left = u.obj V := by rw [← pullbackProj_obj p u Z]; exact hY
  obtain ⟨c, hc⟩ := u.map_surjective (eqToHom hZl.symm ≫ Z.hom)
  have hZhom : Z.hom = eqToHom hZl ≫ u.map c := by rw [hc, ← Category.assoc]; simp
  have hZr : p.obj Z.right = p.obj Z.right := rfl
  set z : 𝒮 := Functor.IsPreFibered.pullbackObj hZr c with hzdef
  set τ : z ⟶ Z.right := Functor.IsPreFibered.pullbackMap hZr c with hτdef
  have hτc : p.IsStronglyCartesian c τ := inferInstance
  have hz : p.obj z = V := Functor.IsPreFibered.pullbackObj_proj hZr c
  have hτmap : p.map τ = eqToHom hz ≫ c ≫ eqToHom hZr := IsHomLift.fac' p c τ
  have hτsc : p.IsStronglyCartesian (p.map τ) τ := by
    rw [hτmap]
    exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom hz hZr c τ hτc
  -- The canonical morphism `c_Z : Z ⟶ ι(w)`, strongly cartesian over `u(c)`.
  have h1 : (pullbackProj p u).IsStronglyCartesian (u.map c)
      ((idBaseStronglyCartesian p u).Q.map (toPullbackUnit p u Z)) := by
    refine Functor.IsStronglyCartesian.of_eqToHom_comp hZl (u.map c) _ ?_
    rw [← hZhom]
    exact isStronglyCartesian_Q_toPullbackUnit p u hu Z
  -- The image of `ι(τ)`, strongly cartesian over `u(c)` as well.
  have h2 : (pullbackProj p u).IsStronglyCartesian (u.map c)
      ((idBaseStronglyCartesian p u).Q.map ((pullbackUnit p u).map τ)) := by
    refine Functor.IsStronglyCartesian.of_eqToHom_comp (congrArg u.obj hz) (u.map c) _ ?_
    have h0 := isStronglyCartesian_Q_pullbackUnit_map p u hu τ hτsc
    rwa [hτmap, eqToHom_refl, Category.comp_id, u.map_comp, eqToHom_map] at h0
  have := h1
  have := h2
  refine ⟨z, hz, Functor.IsCartesian.domainUniqueUpToIso (pullbackProj p u) (u.map c)
    ((idBaseStronglyCartesian p u).Q.map ((pullbackUnit p u).map τ))
    ((idBaseStronglyCartesian p u).Q.map (toPullbackUnit p u Z)), ?_⟩
  exact Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift (pullbackProj p u) (u.map c)
    ((idBaseStronglyCartesian p u).Q.map ((pullbackUnit p u).map τ))
    ((idBaseStronglyCartesian p u).Q.map (toPullbackUnit p u Z))

end

end Unit

/-! ### Full faithfulness from full faithfulness on fibres -/

section Fibrewise

universe v vb v' u₂' u₃'

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂'} [Category.{v} 𝒳]
  {𝒴 : Type u₃'} [Category.{v'} 𝒴] {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} [p.IsFibered] [r.IsFibered]
  {F : 𝒳 ⥤ 𝒴} (hF : p.IsFibredOneMorphism r F)

include hF
omit [r.IsFibered]

/-- **A 1-morphism of fibred categories which is faithful on every fibre is faithful.** Every
morphism of `𝒳` factors as a morphism lying over an identity followed by a chosen cartesian lift;
the image of the lift is again cartesian, so it cancels, and the fibre hypothesis applies to the
first factor. This is the analogue for fibred categories of the groupoid statement
`CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber` (Stacks 003Z). -/
@[sga "1 VI 6.10" "Faithfulness clause"]
lemma faithful_of_fiber_faithful
    (h : ∀ U : 𝒞, (Functor.Fiber.mapOfComp p r F hF.comp_eq U).Faithful) : F.Faithful := by
  refine ⟨fun {x y} φ₁ φ₂ hφ => ?_⟩
  have e₁ := Functor.map_eq_of_comp_eq p r F hF.comp_eq φ₁
  have e₂ := Functor.map_eq_of_comp_eq p r F hF.comp_eq φ₂
  rw [hφ] at e₁
  have hbase : p.map φ₁ = p.map φ₂ := e₁.trans e₂.symm
  obtain ⟨w, χ, hχ0⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := y) (p.map φ₁)
  have hχ : p.IsStronglyCartesian (p.map φ₁) χ := inferInstance
  have hχc : p.IsCartesian (p.map φ₁) χ := inferInstance
  have hl₂ : p.IsHomLift (p.map φ₁) φ₂ := by rw [hbase]; infer_instance
  have := hl₂
  set α₁ := Functor.IsCartesian.map p (p.map φ₁) χ φ₁ with hα₁
  set α₂ := Functor.IsCartesian.map p (p.map φ₁) χ φ₂ with hα₂
  have hv₁ : p.IsHomLift (𝟙 (p.obj x)) α₁ := inferInstance
  have hv₂ : p.IsHomLift (𝟙 (p.obj x)) α₂ := inferInstance
  have hFv₁ : r.IsHomLift (𝟙 (p.obj x)) (F.map α₁) :=
    (Functor.isHomLift_map_iff_of_comp_eq p r F hF.comp_eq (𝟙 (p.obj x)) α₁).2 hv₁
  have hFv₂ : r.IsHomLift (𝟙 (p.obj x)) (F.map α₂) :=
    (Functor.isHomLift_map_iff_of_comp_eq p r F hF.comp_eq (𝟙 (p.obj x)) α₂).2 hv₂
  have hFχ : r.IsStronglyCartesian (p.map φ₁) (F.map χ) :=
    hF.map_isStronglyCartesian (p.map φ₁) χ hχ
  have hFχc : r.IsCartesian (p.map φ₁) (F.map χ) := have := hFχ; inferInstance
  have hFα : F.map α₁ = F.map α₂ := by
    have := hFχc
    have := hFv₁
    have := hFv₂
    refine Functor.IsCartesian.ext r (p.map φ₁) (F.map χ) (F.map α₁) (F.map α₂) ?_
    rw [← F.map_comp, ← F.map_comp, hα₁, hα₂, Functor.IsCartesian.fac, Functor.IsCartesian.fac, hφ]
  have hα : α₁ = α₂ := by
    have := hv₁
    have := hv₂
    exact Functor.map_injective_of_fiber_faithful p r F hF.comp_eq (p.obj x) (h _) α₁ α₂ hFα
  have f₁ : α₁ ≫ χ = φ₁ := Functor.IsCartesian.fac p (p.map φ₁) χ φ₁
  have f₂ : α₂ ≫ χ = φ₂ := Functor.IsCartesian.fac p (p.map φ₁) χ φ₂
  rw [← f₁, ← f₂, hα]

/-- **A 1-morphism of fibred categories which is full on every fibre is full.** A morphism
`ψ : F x ⟶ F y` of `𝒴` lies over a morphism `g` of `𝒞`; the image under `F` of the chosen
cartesian lift of `g` at `y` is cartesian, so `ψ` factors through it by a vertical morphism, and
the fibre hypothesis lifts that factor to `𝒳`. This is the analogue for fibred categories of the
groupoid statement `CategoryTheory.Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber`
(Stacks 003Z). -/
lemma full_of_fiber_full
    (h : ∀ U : 𝒞, (Functor.Fiber.mapOfComp p r F hF.comp_eq U).Full) : F.Full := by
  refine ⟨fun {x y} ψ => ?_⟩
  have hox : r.obj (F.obj x) = p.obj x := Functor.congr_obj hF.comp_eq x
  have hoy : r.obj (F.obj y) = p.obj y := Functor.congr_obj hF.comp_eq y
  have hψ : r.IsHomLift (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) ψ := by
    refine IsHomLift.of_fac' r _ ψ hox hoy ?_
    simp
  obtain ⟨w, χ, hχ0⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := y)
    (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy)
  have hχ : p.IsStronglyCartesian (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) χ := inferInstance
  have hwo : p.obj w = p.obj x :=
    IsHomLift.domain_eq p (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) χ
  have hFχ : r.IsStronglyCartesian (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) (F.map χ) :=
    hF.map_isStronglyCartesian _ χ hχ
  have hFχc : r.IsCartesian (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) (F.map χ) :=
    have := hFχ; inferInstance
  have := hFχc
  have := hψ
  set t : F.obj x ⟶ F.obj w :=
    Functor.IsCartesian.map r (eqToHom hox.symm ≫ r.map ψ ≫ eqToHom hoy) (F.map χ) ψ with ht
  have htv : r.IsHomLift (𝟙 (p.obj x)) t := inferInstance
  have := htv
  set tt : (Functor.Fiber.mapOfComp p r F hF.comp_eq (p.obj x)).obj
      (Functor.Fiber.mk (rfl : p.obj x = p.obj x)) ⟶
      (Functor.Fiber.mapOfComp p r F hF.comp_eq (p.obj x)).obj (Functor.Fiber.mk hwo) :=
    Functor.Fiber.homMk r (p.obj x) t with htt
  obtain ⟨aa, haa⟩ := (h (p.obj x)).map_surjective tt
  refine ⟨Functor.Fiber.fiberInclusion.map aa ≫ χ, ?_⟩
  have hFs : F.map (Functor.Fiber.fiberInclusion.map aa) = t := by
    rw [← Functor.Fiber.fiberInclusion_map_mapOfComp_map p r F hF.comp_eq (p.obj x) aa, haa, htt]
    exact Functor.Fiber.fiberInclusion_homMk r (p.obj x) t
  rw [F.map_comp, hFs, ht, Functor.IsCartesian.fac]

end Fibrewise

/-! ### Full faithfulness of a lift into a pushforward -/

/-- A full functor `F` over a faithful `u` has a full lift `𝒮 ⥤ u^p 𝒯`. -/
private lemma full_liftFib_of_full {𝒞 : Type*} [Category.{_} 𝒞] {𝒟 : Type*} [Category.{_} 𝒟]
    {𝒮 : Type*} [Category.{_} 𝒮] {𝒯 : Type*} [Category.{_} 𝒯] {p : 𝒮 ⥤ 𝒞} {u : 𝒞 ⥤ 𝒟}
    {t : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯} (h : F ⋙ t = p ⋙ u) [F.Full] [u.Faithful] :
    (StrictPullback.liftFib p F h).Full := by
  refine ⟨fun {x y} f => ?_⟩
  obtain ⟨ξ, hξ⟩ := F.map_surjective f.fib
  refine ⟨ξ, StrictPullback.Hom.ext ?_ hξ⟩
  have hover : t.map f.fib =
      eqToHom ((StrictPullback.liftFib p F h).obj x).over ≫ u.map f.base ≫
        eqToHom ((StrictPullback.liftFib p F h).obj y).over.symm := f.over
  have hFξ : t.map (F.map ξ) = eqToHom (Functor.congr_obj h x) ≫ u.map (p.map ξ) ≫
      eqToHom (Functor.congr_obj h y).symm := by
    simpa using Functor.congr_hom h ξ
  apply u.map_injective
  rw [hξ, hover] at hFξ
  exact ((cancel_mono _).1 ((cancel_epi _).1 hFξ)).symm

section LiftFib

universe v' w' u₂' u₃' u₄' u₅'

variable {𝒞 : Type u₂'} [Category.{v'} 𝒞] {𝒟 : Type u₃'} [Category.{w'} 𝒟]
  {𝒮 : Type u₄'} [Category.{v'} 𝒮] {𝒯 : Type u₅'} [Category.{w'} 𝒯]

/-- A functor `F : 𝒮 ⥤ 𝒯` over `u` is faithful as soon as its lift `𝒮 ⥤ u^p 𝒯` is, and
conversely: a morphism of `u^p 𝒯` is a pair whose `𝒯`-component is the value of `F`. -/
lemma faithful_liftFib {p : 𝒮 ⥤ 𝒞} {u : 𝒞 ⥤ 𝒟} {t : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯}
    (h : F ⋙ t = p ⋙ u) [F.Faithful] : (StrictPullback.liftFib p F h).Faithful :=
  ⟨fun {_ _} _ _ hξ => F.map_injective (congrArg StrictPullback.Hom.fib hξ)⟩

/-- A functor `F : 𝒮 ⥤ 𝒯` over a **faithful** `u` which is full has a full lift `𝒮 ⥤ u^p 𝒯`: the
`𝒯`-component of a morphism of `u^p 𝒯` comes from `𝒮`, and faithfulness of `u` forces the
`𝒞`-component to be its image. -/
lemma full_liftFib {p : 𝒮 ⥤ 𝒞} {u : 𝒞 ⥤ 𝒟} {t : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯}
    (h : F ⋙ t = p ⋙ u) [F.Full] [u.Faithful] : (StrictPullback.liftFib p F h).Full :=
  full_liftFib_of_full h

end LiftFib

/-- For a fully faithful 1-morphism, `morMapAt` on pulled-back fibres is bijective. -/
private lemma bijective_morMapAt {𝒞 : Type*} [Category.{_} 𝒞] {𝒳 : Type*} [Category.{_} 𝒳]
    {𝒴 : Type*} [Category.{_} 𝒴] {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} [p.IsFibered] [r.IsFibered]
    {F : 𝒳 ⥤ 𝒴} [F.Full] [F.Faithful] (hF : p.IsFibredOneMorphism r F) {U : 𝒞} (x y : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) : Function.Bijective (hF.morMapAt x y f) := by
  have : (Functor.fiberFunctorOfCompEq hF.comp_eq V).Full :=
    Functor.Fiber.full_mapOfComp hF.comp_eq V
  have : (Functor.fiberFunctorOfCompEq hF.comp_eq V).Faithful :=
    Functor.Fiber.faithful_mapOfComp hF.comp_eq V
  exact (Iso.homCongr (hF.mapPullbackFiberIso x f).symm
    (hF.mapPullbackFiberIso y f).symm).bijective.comp
    ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _)

/-! ### The morphism presheaves of a fully faithful 1-morphism -/

section MorPresheafIso

universe v v' u₂'' u₃''

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒳 : Type u₂''} [Category.{v'} 𝒳]
  {𝒴 : Type u₃''} [Category.{v'} 𝒴] {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} [p.IsFibered] [r.IsFibered]
  {F : 𝒳 ⥤ 𝒴} (hF : p.IsFibredOneMorphism r F)

include hF in
/-- **The map of morphism presheaves induced by a fully faithful 1-morphism is an
isomorphism.** Over each object of `𝒞/U` it is the action of the induced functor on fibres,
conjugated by the comparison isomorphisms between the chosen pullbacks, and a fully faithful
1-morphism induces a fully faithful functor on every fibre. -/
lemma isIso_morPresheafMap_of_fullyFaithful [F.Full] [F.Faithful] {U : 𝒞} (x y : p.Fiber U) :
    IsIso (hF.morPresheafMap x y) := by
  have happ : ∀ g, IsIso ((hF.morPresheafMap x y).app g) := fun g => by
    rw [isIso_iff_bijective]
    exact bijective_morMapAt hF x y g.unop.hom
  exact NatIso.isIso_of_isIso_app _

include hF in
/-- **The induced functor on a fibre is bijective on a hom-set as soon as the induced map of
morphism presheaves is bijective on sections over the terminal object of `𝒞/U`.** Over the
terminal object the map of presheaves *is* the action of the functor on fibres, conjugated by the
comparison isomorphisms between the chosen pullbacks along the identity and the objects
themselves. -/
lemma bijective_fiberFunctor_map_of_bijective_app {U : 𝒞} (x y : p.Fiber U)
    (hb : Function.Bijective
      ((hF.morPresheafMap x y).app (Opposite.op (Over.mk (𝟙 U))))) :
    Function.Bijective
      (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hF.comp_eq U).map m) := by
  set Φx := (Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x with hΦx
  set Φy := (Functor.fiberFunctorOfCompEq hF.comp_eq U).obj y with hΦy
  set eα : (x ⟶ y) ≃ (Functor.pullbackFiber p x (𝟙 U) ⟶ Functor.pullbackFiber p y (𝟙 U)) :=
    Iso.homCongr (Functor.pullbackFiberIdIso x).symm (Functor.pullbackFiberIdIso y).symm with heα
  set eγ : (Φx ⟶ Φy) ≃
      (Functor.pullbackFiber r Φx (𝟙 U) ⟶ Functor.pullbackFiber r Φy (𝟙 U)) :=
    Iso.homCongr (Functor.pullbackFiberIdIso Φx).symm
      (Functor.pullbackFiberIdIso Φy).symm with heγ
  have hθx : (Functor.pullbackFiberIdIso Φx).hom =
      (hF.mapPullbackFiberIso x (𝟙 U)).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq U).map (Functor.pullbackFiberIdIso x).hom := by
    have h := Functor.IsFibredOneMorphism.mapPullbackFiberIso_id_inv_comp hF x
    rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hθy : (Functor.pullbackFiberIdIso Φy).hom =
      (hF.mapPullbackFiberIso y (𝟙 U)).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq U).map (Functor.pullbackFiberIdIso y).hom := by
    have h := Functor.IsFibredOneMorphism.mapPullbackFiberIso_id_inv_comp hF y
    rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have htail :
      (Functor.fiberFunctorOfCompEq hF.comp_eq U).map (Functor.pullbackFiberIdIso y).inv ≫
          (hF.mapPullbackFiberIso y (𝟙 U)).inv =
        (Functor.pullbackFiberIdIso Φy).inv := by
    rw [← cancel_epi (Functor.pullbackFiberIdIso Φy).hom, Iso.hom_inv_id, hθy]
    simp
  have hsquare : ∀ n : x ⟶ y,
      (hF.morPresheafMap x y).app (Opposite.op (Over.mk (𝟙 U))) (eα n) =
        eγ ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map n) := by
    intro n
    rw [Functor.IsFibredOneMorphism.morPresheafMap_app, heα, heγ]
    simp only [Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom, Functor.map_comp, Category.assoc]
    rw [← htail, hθx]
    simp [Over.mk_left, Over.mk_hom, Category.assoc]
  have hfun : (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hF.comp_eq U).map m) =
      eγ.symm ∘ (fun n : x ⟶ y =>
        (hF.morPresheafMap x y).app (Opposite.op (Over.mk (𝟙 U))) (eα n)) := by
    funext n
    rw [Function.comp_apply, hsquare n, Equiv.symm_apply_apply]
  rw [hfun]
  exact eγ.symm.bijective.comp (hb.comp eα.bijective)

end MorPresheafIso

/-! ### Post-composition with an equivalence of fibred categories -/

section Postcomp

universe v uA uB uC

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒮 : Type uA} [Category.{v} 𝒮]
  {𝒮' : Type uB} [Category.{v} 𝒮'] {𝒯 : Type uC} [Category.{v} 𝒯]
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {t : 𝒯 ⥤ 𝒞} {Kc : 𝒮' ⥤ 𝒯}

/-- Lying over the identity of an object only depends on that object. -/
lemma isHomLift_id_congr {R R' : 𝒞} (h : R = R') {a b : 𝒯} (φ : a ⟶ b)
    (hφ : t.IsHomLift (𝟙 R) φ) : t.IsHomLift (𝟙 R') φ := by
  subst h
  exact hφ

/-- **Post-composition with a 1-morphism of fibred categories over `𝒞`**, as a functor of the
morphism categories of Stacks 02ZG. -/
def postcompFibredMor (hKc : p'.IsFibredOneMorphism t Kc) :
    Functor.FibredMor p p' ⥤ Functor.FibredMor p t where
  obj K := ⟨K.functor ⋙ Kc, K.isFibredOneMorphism.comp hKc⟩
  map {_ _} α := ⟨Functor.whiskerRight α.trans Kc, fun A =>
    (Functor.isHomLift_map_iff_of_comp_eq p' t Kc hKc.comp_eq (𝟙 (p.obj A))
      (α.trans.app A)).2 (α.isHomLift A)⟩
  map_id _ := Functor.FibredMor.Hom.ext' (by ext A; simp)
  map_comp _ _ := Functor.FibredMor.Hom.ext' (by ext A; simp)

/-- The underlying functor of `postcompFibredMor hKc` applied to `K` is `K.functor ⋙ Kc`. -/
@[simp]
lemma postcompFibredMor_obj_functor (hKc : p'.IsFibredOneMorphism t Kc)
    (K : Functor.FibredMor p p') :
    ((postcompFibredMor (p := p) hKc).obj K).functor = K.functor ⋙ Kc := rfl

/-- The transformation underlying `postcompFibredMor hKc` applied to `α` is `α.trans` whiskered
by `Kc`. -/
@[simp]
lemma postcompFibredMor_map_trans (hKc : p'.IsFibredOneMorphism t Kc)
    {K L : Functor.FibredMor p p'} (α : K ⟶ L) :
    ((postcompFibredMor (p := p) hKc).map α).trans = Functor.whiskerRight α.trans Kc := rfl

/-- Post-composition with a faithful 1-morphism is faithful. -/
lemma faithful_postcompFibredMor (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Faithful] :
    (postcompFibredMor (p := p) hKc).Faithful where
  map_injective {_ _} α β h := by
    refine Functor.FibredMor.Hom.ext' (NatTrans.ext (funext fun A => ?_))
    have h' : Functor.whiskerRight α.trans Kc = Functor.whiskerRight β.trans Kc :=
      congrArg Functor.FibredMor.Hom.trans h
    have h2 := NatTrans.congr_app h' A
    exact Kc.map_injective (by simpa using h2)

/-- Post-composition with a fully faithful 1-morphism is full. -/
lemma full_postcompFibredMor (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Full] [Kc.Faithful] :
    (postcompFibredMor (p := p) hKc).Full where
  map_surjective {K L} τ := by
    refine ⟨⟨{ app := fun A => Kc.preimage (τ.trans.app A)
               naturality := fun A B m => Kc.map_injective (by
                 simp only [Functor.map_comp, Functor.map_preimage]
                 exact τ.trans.naturality m) }, fun A => ?_⟩, ?_⟩
    · refine (Functor.isHomLift_map_iff_of_comp_eq p' t Kc hKc.comp_eq (𝟙 (p.obj A))
        (Kc.preimage (τ.trans.app A))).1 ?_
      rw [Functor.map_preimage]
      exact τ.isHomLift A
    · refine Functor.FibredMor.Hom.ext' (NatTrans.ext (funext fun A => ?_))
      simp

/-- Post-composition with an equivalence of fibred categories over `𝒞` is essentially
surjective: a 1-morphism into the target is the post-composition of its composite with the
quasi-inverse, up to the counit. -/
lemma essSurj_postcompFibredMor (hKc : p'.IsFibredOneMorphism t Kc)
    {H : 𝒯 ⥤ 𝒮'} (hH : t.IsFibredOneMorphism p' H) (ε : H ⋙ Kc ≅ 𝟭 𝒯)
    (hε : ∀ y : 𝒯, t.IsHomLift (𝟙 (t.obj y)) (ε.hom.app y)) :
    (postcompFibredMor (p := p) hKc).EssSurj where
  mem_essImage M := by
    refine ⟨⟨M.functor ⋙ H, M.isFibredOneMorphism.comp hH⟩, ⟨?_⟩⟩
    refine Functor.FibredMor.isoMk (Functor.isoWhiskerLeft M.functor ε) (fun A => ?_)
    exact isHomLift_id_congr (M.obj_eq A) _ (hε (M.functor.obj A))

/-- **Post-composition with an equivalence in the 2-category of fibred categories over `𝒞`
is an equivalence of morphism categories.** -/
noncomputable def postcompFibredMorEquivalence
    (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Full] [Kc.Faithful]
    {H : 𝒯 ⥤ 𝒮'} (hH : t.IsFibredOneMorphism p' H) (ε : H ⋙ Kc ≅ 𝟭 𝒯)
    (hε : ∀ y : 𝒯, t.IsHomLift (𝟙 (t.obj y)) (ε.hom.app y)) :
    Functor.FibredMor p p' ≌ Functor.FibredMor p t :=
  haveI := faithful_postcompFibredMor (p := p) hKc
  haveI := full_postcompFibredMor (p := p) hKc
  haveI := essSurj_postcompFibredMor (p := p) hKc hH ε hε
  haveI : (postcompFibredMor (p := p) hKc).IsEquivalence := {}
  (postcompFibredMor (p := p) hKc).asEquivalence

end Postcomp

/-! ### The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` -/

/-- A locally bijective `φ` restricted along a cocontinuous `v` between sheaves is bijective. -/
private lemma bijective_app_of_isSheaf_whisker {C D : Type*} [Category.{_} C] [Category.{_} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (v : C ⥤ D) [v.IsCocontinuous J K]
    {P Q : Dᵒᵖ ⥤ Type v₃} (φ : P ⟶ Q) [Presheaf.IsLocallyInjective K φ]
    [Presheaf.IsLocallySurjective K φ] (hP : Presheaf.IsSheaf J (v.op ⋙ P))
    (hQ : Presheaf.IsSheaf J (v.op ⋙ Q)) (X : C) :
    Function.Bijective (φ.app (Opposite.op (v.obj X))) := by
  have := Presheaf.isLocallyInjective_whisker J K v φ
  have := Presheaf.isLocallySurjective_whisker J K v φ
  let Ψ : (⟨_, hP⟩ : Sheaf J _) ⟶ ⟨_, hQ⟩ := ⟨Functor.whiskerLeft v.op φ⟩
  have := (Sheaf.isLocallyBijective_iff_isIso Ψ).1 ⟨inferInstance, inferInstance⟩
  rw [← isIso_iff_bijective]
  exact inferInstanceAs (IsIso (((sheafToPresheaf J _).map Ψ).app (Opposite.op X)))

/-- Every `y` is isomorphic to some `F x` by an isomorphism over the identity of `t y`. -/
private lemma exists_vertical_iso_of_isEquivalenceOver {𝒞 : Type*} [Category.{_} 𝒞]
    {𝒮 : Type*} [Category.{_} 𝒮] {𝒯 : Type*} [Category.{_} 𝒯] {p : 𝒮 ⥤ 𝒞} {t : 𝒯 ⥤ 𝒞}
    {F : 𝒮 ⥤ 𝒯} (E : Functor.IsEquivalenceOver p t F) (hF : F ⋙ t = p) (y : 𝒯) :
    ∃ (x : 𝒮) (e : F.obj x ≅ y), t.IsHomLift (𝟙 (t.obj y)) e.hom := by
  refine ⟨E.inv.obj y, E.counitIso.app y, ?_⟩
  have hb : t.obj ((E.inv ⋙ F).obj y) = t.obj y :=
    (Functor.congr_obj hF (E.inv.obj y)).trans (Functor.congr_obj E.inv_over y)
  rw [← hb]
  exact E.counit_vertical y

/-- The lift of the unit `ι` into the pushforward of `u_p 𝒮` is a fibred 1-morphism. -/
private lemma isFibredOneMorphism_liftFib_pullbackUnitLoc {𝒞 : Type*} [Category.{_} 𝒞]
    {𝒟 : Type*} [Category.{_} 𝒟] {𝒮 : Type*} [Category.{_} 𝒮] (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)
    [p.IsFibered] [Limits.HasFiniteLimits 𝒞] [Limits.PreservesFiniteLimits u] :
    p.IsFibredOneMorphism (StrictPullback.structureFunctor u (pullbackProj p u))
      (StrictPullback.liftFib p (pullbackUnitLoc p u) (pullbackUnitLoc_comp_pullbackProj p u)) := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  refine PullbackAdjunction.isFibredOneMorphism_of_exists_lift _ _ _ rfl ?_
  intro b V β
  obtain ⟨a, g, hg⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := b) β
  have hgs : p.IsStronglyCartesian β g := inferInstance
  refine ⟨a, g, hgs, ?_⟩
  refine PullbackAdjunction.isStronglyCartesian_liftFib_map p u (pullbackProj p u)
    (pullbackUnitLoc_comp_pullbackProj p u) β g hgs ?_
  have hβ : p.map g = eqToHom (IsHomLift.domain_eq p β g) ≫ β ≫
      eqToHom (IsHomLift.codomain_eq p β g).symm := IsHomLift.fac' p β g
  have hsc : p.IsStronglyCartesian (p.map g) g := by
    rw [hβ]
    exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom _ _ _ _ hgs
  have hQ := isStronglyCartesian_Q_pullbackUnit_map p u (fun _ => inferInstance) g hsc
  rw [hβ] at hQ
  simp only [Functor.map_comp, eqToHom_map, eqToHom_refl, Category.comp_id] at hQ
  exact Functor.IsStronglyCartesian.of_eqToHom_comp _ _ _ hQ

section Canonical

universe v u₄

open Limits

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type v} [Category.{v} 𝒟]
  {𝒮 : Type v} [Category.{v} 𝒮] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}
  (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)

/-- An isomorphism of the fibre of `q` over `u V` between the `𝒳`-components of two objects of
`u^p 𝒳` lying over `V` is an isomorphism of the fibre of `u^p 𝒳` over `V`. -/
noncomputable def fiberIsoOfFib {V : 𝒞}
    {X Y : (StrictPullback.structureFunctor u q).Fiber V}
    (e : StrictPullback.fiberFib X ≅ StrictPullback.fiberFib Y) : X ≅ Y :=
  Functor.Fiber.isoMk
    { hom := StrictPullback.fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map e.hom) e.hom.2
      inv := StrictPullback.fiberHomMk Y.2 X.2 (Functor.Fiber.fiberInclusion.map e.inv) e.inv.2
      hom_inv_id := by
        refine StrictPullback.Hom.ext ?_ ?_
        · simp
        · dsimp only [StrictPullback.structureFunctor_obj, StrictPullback.comp_fib,
              StrictPullback.fiberHomMk_fib, StrictPullback.id_fib]
          rw [← Functor.map_comp, e.hom_inv_id]
          rfl
      inv_hom_id := by
        refine StrictPullback.Hom.ext ?_ ?_
        · simp
        · dsimp only [StrictPullback.structureFunctor_obj, StrictPullback.comp_fib,
              StrictPullback.fiberHomMk_fib, StrictPullback.id_fib]
          rw [← Functor.map_comp, e.inv_hom_id]
          rfl }
    (StrictPullback.isHomLift_fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map e.hom) e.hom.2)

/-- **The unit read as a 1-morphism over `𝒞`**, `𝒮 ⥤ u^p(u_p 𝒮)`, `x ↦ (p(x), ι(x))`. -/
noncomputable def pullbackUnitPush : 𝒮 ⥤ StrictPullback u (pullbackProj p u) :=
  StrictPullback.liftFib p (pullbackUnitLoc p u) (pullbackUnitLoc_comp_pullbackProj p u)

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] in
/-- The unit read over `𝒞` is a 1-morphism of fibred categories: `ι` carries a strongly cartesian
morphism of `𝒮` to a strongly cartesian morphism of `u_p 𝒮` over its image under `u`, by
Stacks 04WG. -/
lemma isFibredOneMorphism_pullbackUnitPush :
    p.IsFibredOneMorphism (StrictPullback.structureFunctor u (pullbackProj p u))
      (pullbackUnitPush p u) := by
  exact isFibredOneMorphism_liftFib_pullbackUnitLoc p u

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [q.IsFibered] in
/-- **The unit read over `𝒞` is fully faithful** when `u` is: this is
`CategoryTheory.Comma.pullbackUnitLoc_full` and
`CategoryTheory.Comma.pullbackUnitLoc_faithful` transported through the lift. -/
lemma fullyFaithful_pullbackUnitPush :
    (pullbackUnitPush p u).Full ∧ (pullbackUnitPush p u).Faithful := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  have h1 := pullbackUnitLoc_full p u (fun _ => inferInstance)
  have h2 := pullbackUnitLoc_faithful p u (fun _ => inferInstance)
  exact ⟨full_liftFib _, faithful_liftFib _⟩

/-- **The canonical 1-morphism `can : 𝒮 ⟶ f_*f⁻¹𝒮` of Stacks 04WS (1).** It is the image of the
stackification `G : u_p 𝒮 ⥤ f⁻¹𝒮` under the functor `A` of Stacks 04WI, that is
`x ↦ (p(x), G(ι(x)))` where `ι` is the unit `CategoryTheory.Comma.pullbackUnitLoc`. This is the
description the source gives of it. -/
noncomputable def pullbackStackCan : 𝒮 ⥤ StrictPullback u q :=
  (PullbackAdjunction.restrictBased p u q ⟨G, hG.comp_eq⟩).toFunctor

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The base of `can(x)` is `p(x)`. -/
@[simp] lemma pullbackStackCan_obj_base (x : 𝒮) :
    ((pullbackStackCan p u hG).obj x).base = p.obj x := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The fibre component of `can(x)` is `G(ι(x))`. -/
@[simp] lemma pullbackStackCan_obj_fib (x : 𝒮) :
    ((pullbackStackCan p u hG).obj x).fib = G.obj ((pullbackUnitLoc p u).obj x) := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The base of `can(α)` is `p(α)`. -/
@[simp] lemma pullbackStackCan_map_base {x y : 𝒮} (α : x ⟶ y) :
    ((pullbackStackCan p u hG).map α).base = p.map α := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The fibre component of `can(α)` is `G(ι(α))`. -/
@[simp] lemma pullbackStackCan_map_fib {x y : 𝒮} (α : x ⟶ y) :
    ((pullbackStackCan p u hG).map α).fib = G.map ((pullbackUnitLoc p u).map α) := rfl

omit [u.Full] [u.Faithful] [q.IsFibered] in
/-- `can` is a 1-morphism of fibred categories over `𝒞`, by Stacks 04WI. -/
lemma isFibredOneMorphism_pullbackStackCan :
    p.IsFibredOneMorphism (StrictPullback.structureFunctor u q) (pullbackStackCan p u hG) :=
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  PullbackAdjunction.isFibredOneMorphism_restrictBased p u q (fun _ => inferInstance) _ hG

omit [u.IsContinuous J K] [u.Faithful] in
/-- **Local essential surjectivity of `can`**, condition (2) of Stacks 046N for the canonical
1-morphism `𝒮 ⟶ f_*f⁻¹𝒮`.

Let `X` be an object of the fibre of `f_*f⁻¹𝒮` over `U`, that is an object of the fibre of `f⁻¹𝒮`
over `u(U)`. Clause (2) of Stacks 02ZN for the stackification `G` gives a `K`-covering sieve of
`u(U)` along whose members `X` comes from `u_p 𝒮`; cocontinuity of `u` pulls that sieve back to a
`J`-covering sieve of `U`, and along its members the object of `u_p 𝒮` lies over an object in the
image of `u`, hence comes from `𝒮` by
`CategoryTheory.Comma.exists_iso_pullbackUnitLoc` — which is where full faithfulness of `u`
enters. -/
theorem locallyEssSurjOnFibers_pullbackStackCan
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.LocallyEssSurjOnFibers (StrictPullback.isFibered_structureFunctor u q)
      (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq J := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  intro U X
  obtain ⟨R', hR', hess⟩ := hobj (u.obj U) (StrictPullback.fiberFib X)
  refine ⟨R'.functorPullback u, u.cover_lift J K hR', ?_⟩
  intro V a ha
  obtain ⟨Y, ⟨eY⟩⟩ := hess (g := u.map a) ha
  obtain ⟨z, hz, e, he⟩ :=
    exists_iso_pullbackUnitLoc p u (fun _ => inferInstance) Y.1 Y.2
  -- The vertical isomorphism `Y ≅ ι(z)` of the fibre of `u_p 𝒮` over `u(V)`.
  set eι : Y ≅ (⟨(pullbackUnitLoc p u).obj z, by
      rw [pullbackUnitLoc_obj, pullbackProj_obj]
      exact congrArg u.obj hz⟩ : (pullbackProj p u).Fiber (u.obj V)) :=
    Functor.Fiber.isoMk e he with heι
  -- Transport it through `G` and compose with the two given comparisons.
  set ε : StrictPullback.fiberFib
      ((Functor.Fiber.mapOfComp p (StrictPullback.structureFunctor u q)
        (pullbackStackCan p u hG) (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq V).obj
          ⟨z, hz⟩) ≅
      StrictPullback.fiberFib
        (Functor.pullbackFiber (StrictPullback.structureFunctor u q) X a) :=
    (((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj V)).mapIso eι).symm ≪≫ eY) ≪≫
      StrictPullback.fiberFibPullbackIso X a with hε
  exact ⟨⟨z, hz⟩, ⟨fiberIsoOfFib u ε⟩⟩

/-! ### Fibrewise full faithfulness of `can` -/

section FibrewiseCan

variable (hs : p.IsStack J) (hq : q.IsStack K)
  (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] hG in
/-- The morphism presheaf of a pushforward, with the universe lift of
`CategoryTheory.StrictPullback.morPresheafFibIso` removed: the hom universes of the two sides
agree here, so the lift is the identity up to a natural isomorphism. -/
noncomputable def morPresheafFibIso' {𝒯 : Type u₄} [Category.{v} 𝒯] {t : 𝒯 ⥤ 𝒟} [t.IsFibered]
    {U : 𝒞} (X Y : (StrictPullback.structureFunctor u t).Fiber U) :
    Functor.morPresheaf (StrictPullback.structureFunctor u t) X Y ≅
      (Over.post (X := U) u).op ⋙
        Functor.morPresheaf t (StrictPullback.fiberFib X) (StrictPullback.fiberFib Y) :=
  StrictPullback.morPresheafFibIso X Y ≪≫
    Functor.isoWhiskerLeft (Over.post (X := U) u).op
      (Functor.isoWhiskerLeft _ uliftFunctorTrivial.{v} ≪≫
        (Functor.morPresheaf t (StrictPullback.fiberFib X) (StrictPullback.fiberFib Y)).rightUnitor)

/-- The object of the fibre of `u_p 𝒮` over `u(U)` attached to an object of the fibre of `𝒮` over
`U` by the unit. -/
noncomputable def unitFiber {U : 𝒞} (x : p.Fiber U) : (pullbackProj p u).Fiber (u.obj U) :=
  ⟨(pullbackUnitLoc p u).obj x.1, by
    rw [pullbackUnitLoc_obj, pullbackProj_obj]
    exact congrArg u.obj x.2⟩

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] hG in
/-- On the fibre over `U`, the fibre component of the image of `x` under `pullbackUnitPush` is
`unitFiber p u x`. -/
lemma fiberFib_unitPush {U : 𝒞} (x : p.Fiber U) :
    StrictPullback.fiberFib ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackUnitPush p u).comp_eq U).obj x) = unitFiber p u x := rfl

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] in
/-- On the fibre over `U`, the fibre component of `can(x)` is the image of `unitFiber p u x` under
the functor induced by `G` on fibres over `u(U)`. -/
lemma fiberFib_can {U : 𝒞} (x : p.Fiber U) :
    StrictPullback.fiberFib ((Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).obj x) =
      (Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiber p u x) := rfl

include hs hq hmor in
/-- **The comparison of morphism presheaves induced by the stackification is bijective on global
sections over `u(U)`, for the objects coming from `𝒮`.**

The presheaf `Mor(ι x, ι y)` on `𝒟/u(U)` restricts along `𝒞/U ⥤ 𝒟/u(U)` to `Mor(x, y)` on `𝒞/U`,
because the unit is a fully faithful 1-morphism over `𝒞` into the pushforward of `u_p 𝒮`; so that
restriction is a sheaf, `𝒮` being a stack. The restriction of `Mor(G ι x, G ι y)` is a sheaf for
the same reason, `f⁻¹𝒮` being a stack and its pushforward therefore a stack (Stacks 04WC). The map
between them is locally bijective, being the restriction along a **cocontinuous** functor of a
locally bijective map (clause (1) of Stacks 02ZN). A locally bijective map of sheaves is an
isomorphism, so it is bijective on sections over the terminal object of `𝒞/U`. -/
theorem bijective_morPresheafMap_unitFiber (U : 𝒞) (x y : p.Fiber U) :
    Function.Bijective ((hG.morPresheafMap (unitFiber p u x) (unitFiber p u y)).app
      (Opposite.op (Over.mk (𝟙 (u.obj U))))) := by
  have hι := isFibredOneMorphism_pullbackUnitPush p u
  obtain ⟨hfull, hfaith⟩ := fullyFaithful_pullbackUnitPush p u
  have := hfull
  have := hfaith
  -- The two presheaves on `𝒞/U`.
  set X := (Functor.fiberFunctorOfCompEq hι.comp_eq U).obj x with hX
  set Y := (Functor.fiberFunctorOfCompEq hι.comp_eq U).obj y with hY
  have hiso : IsIso (hι.morPresheafMap x y) := isIso_morPresheafMap_of_fullyFaithful hι x y
  have := hiso
  set Θ₁ : Functor.morPresheaf p x y ≅
      (Over.post (X := U) u).op ⋙
        Functor.morPresheaf (pullbackProj p u) (unitFiber p u x) (unitFiber p u y) :=
    asIso (hι.morPresheafMap x y) ≪≫ morPresheafFibIso' u X Y with hΘ₁
  set Θ₂ : Functor.morPresheaf (StrictPullback.structureFunctor u q)
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).obj x)
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).obj y) ≅
      (Over.post (X := U) u).op ⋙
        Functor.morPresheaf q ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj
            (unitFiber p u x))
          ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiber p u y)) :=
    morPresheafFibIso' u _ _ with hΘ₂
  -- Both are sheaves on `𝒞/U`.
  have hsh₁ : Presheaf.IsSheaf (J.over U)
      ((Over.post (X := U) u).op ⋙
        Functor.morPresheaf (pullbackProj p u) (unitFiber p u x) (unitFiber p u y)) :=
    (Presheaf.isSheaf_of_iso_iff Θ₁).1 (hs.isMorSheaf U x y)
  have hsh₂ : Presheaf.IsSheaf (J.over U)
      ((Over.post (X := U) u).op ⋙
        Functor.morPresheaf q ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj
            (unitFiber p u x))
          ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiber p u y))) :=
    (Presheaf.isSheaf_of_iso_iff Θ₂).1
      (StrictPullback.isMorSheaf_structureFunctor J K u q hq.isMorSheaf U _ _)
    -- The restriction of the comparison is locally bijective.
  obtain ⟨hinj, hsurj⟩ := hmor (u.obj U) (unitFiber p u x) (unitFiber p u y)
  have := hinj
  have := hsurj
  exact bijective_app_of_obj_eq _ (congrArg Over.mk (u.map_id U))
    (bijective_app_of_isSheaf_whisker (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) _ hsh₁
      hsh₂ (Over.mk (𝟙 U)))

/-- Morphisms of the fibre of `u^p 𝒯` over `V` are exactly morphisms of the fibre of `𝒯` over
`u(V)`: the `𝒞`-component of a morphism lying over an identity is forced. -/
def fiberFibHomEquiv {𝒯 : Type u₄} [Category.{v} 𝒯] {t : 𝒯 ⥤ 𝒟} {V : 𝒞}
    (X Y : (StrictPullback.structureFunctor u t).Fiber V) :
    (X ⟶ Y) ≃ (StrictPullback.fiberFib X ⟶ StrictPullback.fiberFib Y) where
  toFun f := ⟨f.1.fib, StrictPullback.isHomLift_id_fib f.1 f.2⟩
  invFun m := ⟨StrictPullback.fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map m) m.2,
    StrictPullback.isHomLift_fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map m) m.2⟩
  left_inv f := by
    refine Functor.Fiber.hom_ext (StrictPullback.Hom.ext ?_ rfl)
    exact (StrictPullback.base_eq_eqToHom X.2 Y.2 f.1 f.2).symm
  right_inv m := Functor.Fiber.hom_ext rfl

include hs hq hmor in
/-- **The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is fully faithful on every fibre.** The fibre of
`f_*f⁻¹𝒮` over `U` is the fibre of `f⁻¹𝒮` over `u(U)`, the unit is fully faithful, and the
stackification `G` is bijective on the hom-sets of the objects coming from `𝒮` by
`CategoryTheory.Comma.bijective_morPresheafMap_unitFiber`. -/
theorem bijective_fiber_pullbackStackCan (U : 𝒞) (x y : p.Fiber U) :
    Function.Bijective (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).map m) := by
  have hι := isFibredOneMorphism_pullbackUnitPush p u
  obtain ⟨hfull, hfaith⟩ := fullyFaithful_pullbackUnitPush p u
  have := hfull
  have := hfaith
  have hfl : (Functor.fiberFunctorOfCompEq hι.comp_eq U).Full :=
    Functor.Fiber.full_mapOfComp hι.comp_eq U
  have hfa : (Functor.fiberFunctorOfCompEq hι.comp_eq U).Faithful :=
    Functor.Fiber.faithful_mapOfComp hι.comp_eq U
  have hb1 : Function.Bijective
      (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hι.comp_eq U).map m) :=
    ⟨fun _ _ h => hfa.map_injective h, fun n => hfl.map_surjective n⟩
  have hb2 := bijective_fiberFunctor_map_of_bijective_app hG (unitFiber p u x) (unitFiber p u y)
    (bijective_morPresheafMap_unitFiber p u hG hs hq hmor U x y)
  set e1 := fiberFibHomEquiv u ((Functor.fiberFunctorOfCompEq hι.comp_eq U).obj x)
    ((Functor.fiberFunctorOfCompEq hι.comp_eq U).obj y) with he1
  set e2 := fiberFibHomEquiv u ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).obj x)
    ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).obj y) with he2
  have hcomp : ∀ m : x ⟶ y, (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).map m =
      e2.symm ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).map
        (e1 ((Functor.fiberFunctorOfCompEq hι.comp_eq U).map m))) := by
    intro m
    rw [Equiv.eq_symm_apply]
    exact Functor.Fiber.hom_ext rfl
  have hfun : (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq U).map m) =
      e2.symm ∘ ((fun k : unitFiber p u x ⟶ unitFiber p u y =>
          (Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).map k) ∘
        (e1 ∘ (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hι.comp_eq U).map m))) :=
    funext hcomp
  rw [hfun]
  exact e2.symm.bijective.comp (hb2.comp (e1.bijective.comp hb1))

include hs hq hmor in
/-- **The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is fully faithful.** A 1-morphism of fibred
categories which is fully faithful on every fibre is fully faithful. -/
theorem fullyFaithful_pullbackStackCan :
    (pullbackStackCan p u hG).Full ∧ (pullbackStackCan p u hG).Faithful := by
  have hcan := isFibredOneMorphism_pullbackStackCan p u hG
  refine ⟨full_of_fiber_full hcan ?_, faithful_of_fiber_faithful hcan ?_⟩
  · exact fun U => ⟨fun {x y} n =>
      (bijective_fiber_pullbackStackCan p u hG hs hq hmor U x y).surjective n⟩
  · exact fun U => ⟨fun {x y} _ _ h =>
      (bijective_fiber_pullbackStackCan p u hG hs hq hmor U x y).injective h⟩

include hs hq hmor in
/-- **Stacks 04WS (1), for the pullback given by a supplied stackification.** Let `u : 𝒞 ⥤ 𝒟`
satisfy the assumptions of Sites 00XU — continuous, cocontinuous, fully faithful, `𝒞` finitely
complete and `u` left exact — and let `f : 𝒟 ⟶ 𝒞` be the associated morphism of sites. Let `𝒮` be
a stack over `(𝒞, J)` and let `G : u_p 𝒮 ⥤ f⁻¹𝒮` be a stackification of `u_p 𝒮` over `(𝒟, K)` in
the sense of Stacks 02ZN. Then the canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is an **equivalence of
stacks over `𝒞`**: a quasi-inverse strictly over `𝒞`, with vertical unit and counit.

By Stacks 046N it suffices that the canonical 1-morphism be fully faithful and that every object
of a fibre of `f_*f⁻¹𝒮` be locally in its essential image on fibres, which are
`CategoryTheory.Comma.fullyFaithful_pullbackStackCan` and
`CategoryTheory.Comma.locallyEssSurjOnFibers_pullbackStackCan`.

The statement is *conditional on being given a stackification*, which Stacks 02ZN supplies once
assembled. -/
theorem isEquivalenceOver_pullbackStackCan
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Nonempty (Functor.IsEquivalenceOver p (StrictPullback.structureFunctor u q)
      (pullbackStackCan p u hG)) := by
  obtain ⟨hfl, hfa⟩ := fullyFaithful_pullbackStackCan p u hG hs hq hmor
  have := hfl
  have := hfa
  exact (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers hs
    (StrictPullback.isStack_structureFunctor J K u q hq)
    (isFibredOneMorphism_pullbackStackCan p u hG)).2
    (locallyEssSurjOnFibers_pullbackStackCan p u hG hobj)

include hs hq hmor in
/-- The vertical preimages produced by Stacks 04WS (1): every object of `f_*f⁻¹𝒮` is isomorphic,
over an identity of `𝒞`, to the image of an object of `𝒮`. -/
theorem hasVerticalPreimages_pullbackStackCan
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.HasVerticalPreimages p (StrictPullback.structureFunctor u q)
      (pullbackStackCan p u hG) := by
  obtain ⟨E⟩ := isEquivalenceOver_pullbackStackCan p u hG hs hq hmor hobj
  intro y
  have hF := (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq
  obtain ⟨x, e, he⟩ := exists_vertical_iso_of_isEquivalenceOver E hF y
  have := he
  exact ⟨x, (Functor.congr_obj hF x).symm.trans
    (IsHomLift.domain_eq (StrictPullback.structureFunctor u q) (𝟙 _) e.hom), e.symm,
    IsHomLift.lift_id_inv (StrictPullback.structureFunctor u q) _ e⟩

include hs hq hmor in
/-- **Stacks 04WS (1), as data.** Let `u : 𝒞 ⥤ 𝒟` satisfy the assumptions of Sites 00XU —
continuous, cocontinuous, fully faithful, `𝒞` finitely complete and `u` left exact — and let
`f : 𝒟 ⟶ 𝒞` be the associated morphism of sites. Let `𝒮` be a stack over `(𝒞, J)` and let
`G : u_p 𝒮 ⥤ f⁻¹𝒮` exhibit `f⁻¹𝒮` as the stackification of `u_p 𝒮` over `(𝒟, K)` in the sense of
Stacks 02ZN. Then the canonical functor `𝒮 ⟶ f_*f⁻¹𝒮` is an **equivalence of stacks over `𝒞`**:
a quasi-inverse strictly over `𝒞`, together with vertical unit and counit isomorphisms.

By Stacks 046N it suffices that the canonical functor be fully faithful and that every object of a
fibre of `f_*f⁻¹𝒮` be locally in its essential image on fibres, which are
`CategoryTheory.Comma.fullyFaithful_pullbackStackCan` and
`CategoryTheory.Comma.locallyEssSurjOnFibers_pullbackStackCan`.

The statement is *conditional on being given a stackification*, which Stacks 02ZN supplies once
assembled. -/
@[stacks 04WS "(1)"]
noncomputable def equivalenceOverPullbackStackCan
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.IsEquivalenceOver p (StrictPullback.structureFunctor u q)
      (pullbackStackCan p u hG) :=
  haveI := (fullyFaithful_pullbackStackCan p u hG hs hq hmor).1
  haveI := (fullyFaithful_pullbackStackCan p u hG hs hq hmor).2
  Functor.isEquivalenceOver_of_exists_vertical_iso
    (isFibredOneMorphism_pullbackStackCan p u hG).comp_eq
    (hasVerticalPreimages_pullbackStackCan p u hG hs hq hmor hobj)

end FibrewiseCan

end Canonical

/-! ### Stacks 04WS (2): the equivalence of morphism categories -/

section MorphismCategories

universe v u₄ u₅

open Limits

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type v} [Category.{v} 𝒟]
  {𝒮 : Type v} [Category.{v} 𝒮] {𝒮₂ : Type v} [Category.{v} 𝒮₂]
  {𝒳 : Type u₄} [Category.{v} 𝒳] {𝒳₂ : Type u₅} [Category.{v} 𝒳₂]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}
  (p : 𝒮 ⥤ 𝒞) (p₂ : 𝒮₂ ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [p₂.IsFibered]
  [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)
  {q₂ : 𝒳₂ ⥤ 𝒟} [q₂.IsFibered] {G₂ : pullbackLocalization p₂ u ⥤ 𝒳₂}
  (hG₂ : (pullbackProj p₂ u).IsFibredOneMorphism q₂ G₂)
  (hs : p.IsStack J) (hq : q.IsStack K)
  (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))
  (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
    (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g))
  (hs₂ : p₂.IsStack J) (hq₂ : q₂.IsStack K)
  (hmor₂ : ∀ (V : 𝒟) (a b : (pullbackProj p₂ u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG₂.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG₂.morPresheafMap a b))
  (hobj₂ : ∀ (V : 𝒟) (x' : q₂.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
    (Functor.fiberFunctorOfCompEq hG₂.comp_eq W).essImage (Functor.pullbackFiber q₂ x' g))

include hs₂ hq₂ hmor₂ hobj₂ in
/-- The canonical 1-morphism `𝒮₂ ⟶ f_*f⁻¹𝒮₂` is an **equivalence in the 2-category of fibred
categories over `𝒞`**: by Stacks 04WS (1) it is an equivalence over `𝒞`, and
`CategoryTheory.Functor.isFibredEquivalenceOver_of_fullyFaithful` upgrades that to a quasi-inverse
which is again a 1-morphism of fibred categories. -/
theorem isFibredEquivalenceOver_pullbackStackCan :
    Functor.IsFibredEquivalenceOver p₂ (StrictPullback.structureFunctor u q₂)
      (pullbackStackCan p₂ u hG₂) := by
  obtain ⟨E⟩ := isEquivalenceOver_pullbackStackCan p₂ u hG₂ hs₂ hq₂ hmor₂ hobj₂
  obtain ⟨hfl, hfa⟩ := fullyFaithful_pullbackStackCan p₂ u hG₂ hs₂ hq₂ hmor₂
  have := hfl
  have := hfa
  have hKc := isFibredOneMorphism_pullbackStackCan p₂ u hG₂
  have hsurj := exists_vertical_iso_of_isEquivalenceOver E hKc.comp_eq
  have h := Functor.isFibredEquivalenceOver_of_fullyFaithful
    (q := StrictPullback.structureFunctor u q₂) (pullbackStackCan p₂ u hG₂) hsurj
  rwa [hKc.comp_eq] at h

include hs hq hmor hobj hs₂ hq₂ hmor₂ hobj₂ in
/-- **Stacks 04WS (2), for the pullbacks given by supplied stackifications.** Let `u : 𝒞 ⥤ 𝒟`
satisfy the assumptions of Sites 00XU and let `f : 𝒟 ⟶ 𝒞` be the associated morphism of sites.
For stacks `𝒮` and `𝒮₂` over `(𝒞, J)` with pullbacks `f⁻¹𝒮` and `f⁻¹𝒮₂` given by supplied
stackifications of `u_p 𝒮` and `u_p 𝒮₂` (Stacks 04WJ), the morphism categories

`Mor_{Stacks/𝒞}(𝒮, 𝒮₂)`  and  `Mor_{Stacks/𝒟}(f⁻¹𝒮, f⁻¹𝒮₂)`

are canonically equivalent. The equivalence is the composite of post-composition with the
canonical equivalence `𝒮₂ ⟶ f_*f⁻¹𝒮₂` of clause (1) with the adjunction of Stacks 04WK at
`𝒯 = f⁻¹𝒮₂`; the direction `f⁻¹` is its quasi-inverse.

Both clauses are conditional on being given stackifications, which Stacks 02ZN supplies once
assembled. -/
@[stacks 04WS "(2)"]
noncomputable def equivalenceFibredMorPullbackStack :
    Functor.FibredMor p p₂ ≌
      Functor.FibredMor q q₂ :=
  haveI : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  have hfe := isFibredEquivalenceOver_pullbackStackCan p₂ u hG₂ hs₂ hq₂ hmor₂ hobj₂
  have hff := fullyFaithful_pullbackStackCan p₂ u hG₂ hs₂ hq₂ hmor₂
  haveI := hff.1
  haveI := hff.2
  (postcompFibredMorEquivalence (p := p) hfe.isFibredOneMorphism
      hfe.exists_inverse.choose_spec.choose
      hfe.exists_inverse.choose_spec.choose_spec.choose_spec.choose_spec.choose
      hfe.exists_inverse.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec).trans
    (Functor.equivalenceFibredMorPushforwardPullbackStack J K p u hs hq hG hmor hobj hq₂)

end MorphismCategories

/-! ### The morphism presheaves of a fully faithful 1-morphism, in independent universes -/

section MorPresheafIsoULift

universe vb' v₁' v₂' u₁' u₂' u₃'

variable {𝒞 : Type u₁'} [Category.{vb'} 𝒞] {𝒳 : Type u₂'} [Category.{v₁'} 𝒳]
  {𝒴 : Type u₃'} [Category.{v₂'} 𝒴] {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} [p.IsFibered] [r.IsFibered]
  {F : 𝒳 ⥤ 𝒴} (hF : p.IsFibredOneMorphism r F)

include hF in
/-- **The universe-lifted map of morphism presheaves induced by a fully faithful 1-morphism is an
isomorphism**, for total categories with independent hom universes: its sections are the action of
the induced functor on fibres, conjugated by the comparison isomorphisms between the chosen
pullbacks. -/
lemma isIso_morPresheafMapULift_of_fullyFaithful [F.Full] [F.Faithful] {U : 𝒞}
    (x y : p.Fiber U) : IsIso (hF.morPresheafMapULift x y) := by
  have happ : ∀ g, IsIso ((hF.morPresheafMapULift x y).app g) := fun g => by
    rw [isIso_iff_bijective]
    exact Equiv.ulift.symm.bijective.comp
      ((bijective_morMapAt hF x y g.unop.hom).comp Equiv.ulift.bijective)
  exact NatIso.isIso_of_isIso_app _

end MorPresheafIsoULift

/-! ### Full faithfulness of a lift into a pushforward, in independent universes -/

section LiftFibUniv

universe v' w' v'' w'' u₂' u₃' u₄' u₅'

variable {𝒞 : Type u₂'} [Category.{v'} 𝒞] {𝒟 : Type u₃'} [Category.{w'} 𝒟]
  {𝒮 : Type u₄'} [Category.{v''} 𝒮] {𝒯 : Type u₅'} [Category.{w''} 𝒯]

/-- A functor `F : 𝒮 ⥤ 𝒯` over `u` is faithful as soon as its lift `𝒮 ⥤ u^p 𝒯` is, and
conversely: a morphism of `u^p 𝒯` is a pair whose `𝒯`-component is the value of `F`. -/
lemma faithful_liftFib_univ {p : 𝒮 ⥤ 𝒞} {u : 𝒞 ⥤ 𝒟} {t : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯}
    (h : F ⋙ t = p ⋙ u) [F.Faithful] : (StrictPullback.liftFib p F h).Faithful :=
  ⟨fun {_ _} _ _ hξ => F.map_injective (congrArg StrictPullback.Hom.fib hξ)⟩

/-- A functor `F : 𝒮 ⥤ 𝒯` over a **faithful** `u` which is full has a full lift `𝒮 ⥤ u^p 𝒯`: the
`𝒯`-component of a morphism of `u^p 𝒯` comes from `𝒮`, and faithfulness of `u` forces the
`𝒞`-component to be its image. -/
lemma full_liftFib_univ {p : 𝒮 ⥤ 𝒞} {u : 𝒞 ⥤ 𝒟} {t : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯}
    (h : F ⋙ t = p ⋙ u) [F.Full] [u.Faithful] : (StrictPullback.liftFib p F h).Full :=
  full_liftFib_of_full h

end LiftFibUniv

/-! ### Post-composition with an equivalence of fibred categories, in independent universes -/

section PostcompUniv

universe v vA vB vC uA uB uC

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒮 : Type uA} [Category.{vA} 𝒮]
  {𝒮' : Type uB} [Category.{vB} 𝒮'] {𝒯 : Type uC} [Category.{vC} 𝒯]
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {t : 𝒯 ⥤ 𝒞} {Kc : 𝒮' ⥤ 𝒯}

/-- Lying over the identity of an object only depends on that object. -/
lemma isHomLift_id_congr_univ {R R' : 𝒞} (h : R = R') {a b : 𝒯} (φ : a ⟶ b)
    (hφ : t.IsHomLift (𝟙 R) φ) : t.IsHomLift (𝟙 R') φ := by
  subst h
  exact hφ

/-- **Post-composition with a 1-morphism of fibred categories over `𝒞`**, as a functor of the
morphism categories of Stacks 02ZG. -/
def postcompFibredMorUniv (hKc : p'.IsFibredOneMorphism t Kc) :
    Functor.FibredMor p p' ⥤ Functor.FibredMor p t where
  obj K := ⟨K.functor ⋙ Kc, K.isFibredOneMorphism.comp hKc⟩
  map {_ _} α := ⟨Functor.whiskerRight α.trans Kc, fun A =>
    (Functor.isHomLift_map_iff_of_comp_eq p' t Kc hKc.comp_eq (𝟙 (p.obj A))
      (α.trans.app A)).2 (α.isHomLift A)⟩
  map_id _ := Functor.FibredMor.Hom.ext' (by ext A; simp)
  map_comp _ _ := Functor.FibredMor.Hom.ext' (by ext A; simp)

/-- The underlying functor of `postcompFibredMorUniv hKc` applied to `K` is `K.functor ⋙ Kc`. -/
@[simp]
lemma postcompFibredMorUniv_obj_functor (hKc : p'.IsFibredOneMorphism t Kc)
    (K : Functor.FibredMor p p') :
    ((postcompFibredMorUniv (p := p) hKc).obj K).functor = K.functor ⋙ Kc := rfl

/-- The transformation underlying `postcompFibredMorUniv hKc` applied to `α` is `α.trans`
whiskered by `Kc`. -/
@[simp]
lemma postcompFibredMorUniv_map_trans (hKc : p'.IsFibredOneMorphism t Kc)
    {K L : Functor.FibredMor p p'} (α : K ⟶ L) :
    ((postcompFibredMorUniv (p := p) hKc).map α).trans = Functor.whiskerRight α.trans Kc := rfl

/-- Post-composition with a faithful 1-morphism is faithful. -/
lemma faithful_postcompFibredMorUniv (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Faithful] :
    (postcompFibredMorUniv (p := p) hKc).Faithful where
  map_injective {_ _} α β h := by
    refine Functor.FibredMor.Hom.ext' (NatTrans.ext (funext fun A => ?_))
    have h' : Functor.whiskerRight α.trans Kc = Functor.whiskerRight β.trans Kc :=
      congrArg Functor.FibredMor.Hom.trans h
    have h2 := NatTrans.congr_app h' A
    exact Kc.map_injective (by simpa using h2)

/-- Post-composition with a fully faithful 1-morphism is full. -/
lemma full_postcompFibredMorUniv (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Full] [Kc.Faithful] :
    (postcompFibredMorUniv (p := p) hKc).Full where
  map_surjective {K L} τ := by
    refine ⟨⟨{ app := fun A => Kc.preimage (τ.trans.app A)
               naturality := fun A B m => Kc.map_injective (by
                 simp only [Functor.map_comp, Functor.map_preimage]
                 exact τ.trans.naturality m) }, fun A => ?_⟩, ?_⟩
    · refine (Functor.isHomLift_map_iff_of_comp_eq p' t Kc hKc.comp_eq (𝟙 (p.obj A))
        (Kc.preimage (τ.trans.app A))).1 ?_
      rw [Functor.map_preimage]
      exact τ.isHomLift A
    · refine Functor.FibredMor.Hom.ext' (NatTrans.ext (funext fun A => ?_))
      simp

/-- Post-composition with an equivalence of fibred categories over `𝒞` is essentially
surjective: a 1-morphism into the target is the post-composition of its composite with the
quasi-inverse, up to the counit. -/
lemma essSurj_postcompFibredMorUniv (hKc : p'.IsFibredOneMorphism t Kc)
    {H : 𝒯 ⥤ 𝒮'} (hH : t.IsFibredOneMorphism p' H) (ε : H ⋙ Kc ≅ 𝟭 𝒯)
    (hε : ∀ y : 𝒯, t.IsHomLift (𝟙 (t.obj y)) (ε.hom.app y)) :
    (postcompFibredMorUniv (p := p) hKc).EssSurj where
  mem_essImage M := by
    refine ⟨⟨M.functor ⋙ H, M.isFibredOneMorphism.comp hH⟩, ⟨?_⟩⟩
    refine Functor.FibredMor.isoMk (Functor.isoWhiskerLeft M.functor ε) (fun A => ?_)
    exact isHomLift_id_congr_univ (M.obj_eq A) _ (hε (M.functor.obj A))

/-- **Post-composition with an equivalence in the 2-category of fibred categories over `𝒞`
is an equivalence of morphism categories.** -/
noncomputable def postcompFibredMorEquivalenceUniv
    (hKc : p'.IsFibredOneMorphism t Kc) [Kc.Full] [Kc.Faithful]
    {H : 𝒯 ⥤ 𝒮'} (hH : t.IsFibredOneMorphism p' H) (ε : H ⋙ Kc ≅ 𝟭 𝒯)
    (hε : ∀ y : 𝒯, t.IsHomLift (𝟙 (t.obj y)) (ε.hom.app y)) :
    Functor.FibredMor p p' ≌ Functor.FibredMor p t :=
  haveI := faithful_postcompFibredMorUniv (p := p) hKc
  haveI := full_postcompFibredMorUniv (p := p) hKc
  haveI := essSurj_postcompFibredMorUniv (p := p) hKc hH ε hε
  haveI : (postcompFibredMorUniv (p := p) hKc).IsEquivalence := {}
  (postcompFibredMorUniv (p := p) hKc).asEquivalence

end PostcompUniv

/-! ### Fibres of a pushforward, in independent universes -/

section PushforwardFibre

universe vc vd vx u₂'' u₃''

open Limits

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂''} [Category.{vd} 𝒟]
  {𝒳 : Type u₃''} [Category.{vx} 𝒳]

/-- An isomorphism of the fibre of `q` over `u V` between the `𝒳`-components of two objects of
`u^p 𝒳` lying over `V` is an isomorphism of the fibre of `u^p 𝒳` over `V`. -/
noncomputable def fiberIsoOfFibUniv (u : 𝒞 ⥤ 𝒟) {q : 𝒳 ⥤ 𝒟} {V : 𝒞}
    {X Y : (StrictPullback.structureFunctor u q).Fiber V}
    (e : StrictPullback.fiberFib X ≅ StrictPullback.fiberFib Y) : X ≅ Y :=
  Functor.Fiber.isoMk
    { hom := StrictPullback.fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map e.hom) e.hom.2
      inv := StrictPullback.fiberHomMk Y.2 X.2 (Functor.Fiber.fiberInclusion.map e.inv) e.inv.2
      hom_inv_id := by
        refine StrictPullback.Hom.ext ?_ ?_
        · simp
        · dsimp only [StrictPullback.structureFunctor_obj, StrictPullback.comp_fib,
              StrictPullback.fiberHomMk_fib, StrictPullback.id_fib]
          rw [← Functor.map_comp, e.hom_inv_id]
          rfl
      inv_hom_id := by
        refine StrictPullback.Hom.ext ?_ ?_
        · simp
        · dsimp only [StrictPullback.structureFunctor_obj, StrictPullback.comp_fib,
              StrictPullback.fiberHomMk_fib, StrictPullback.id_fib]
          rw [← Functor.map_comp, e.inv_hom_id]
          rfl }
    (StrictPullback.isHomLift_fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map e.hom) e.hom.2)

/-- Morphisms of the fibre of `u^p 𝒯` over `V` are exactly morphisms of the fibre of `𝒯` over
`u(V)`: the `𝒞`-component of a morphism lying over an identity is forced. -/
def fiberFibHomEquivUniv (u : 𝒞 ⥤ 𝒟) {t : 𝒳 ⥤ 𝒟} {V : 𝒞}
    (X Y : (StrictPullback.structureFunctor u t).Fiber V) :
    (X ⟶ Y) ≃ (StrictPullback.fiberFib X ⟶ StrictPullback.fiberFib Y) where
  toFun f := ⟨f.1.fib, StrictPullback.isHomLift_id_fib f.1 f.2⟩
  invFun m := ⟨StrictPullback.fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map m) m.2,
    StrictPullback.isHomLift_fiberHomMk X.2 Y.2 (Functor.Fiber.fiberInclusion.map m) m.2⟩
  left_inv f := by
    refine Functor.Fiber.hom_ext (StrictPullback.Hom.ext ?_ rfl)
    exact (StrictPullback.base_eq_eqToHom X.2 Y.2 f.1 f.2).symm
  right_inv m := Functor.Fiber.hom_ext rfl

end PushforwardFibre

/-! ### The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮`, in independent universes -/

section CanonicalUniv

universe vc vd vs u₄

open Limits

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂} [Category.{vd} 𝒟]
  {𝒮 : Type u₃} [Category.{vs} 𝒮] {𝒳 : Type u₄} [Category.{max u₂ u₃ vd vs} 𝒳]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}
  (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)

/-- **The unit read as a 1-morphism over `𝒞`**, `𝒮 ⥤ u^p(u_p 𝒮)`, `x ↦ (p(x), ι(x))`. -/
noncomputable def pullbackUnitPushUniv : 𝒮 ⥤ StrictPullback u (pullbackProj p u) :=
  StrictPullback.liftFib p (pullbackUnitLoc p u) (pullbackUnitLoc_comp_pullbackProj p u)

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] in
/-- The unit read over `𝒞` is a 1-morphism of fibred categories: `ι` carries a strongly cartesian
morphism of `𝒮` to a strongly cartesian morphism of `u_p 𝒮` over its image under `u`, by
Stacks 04WG. -/
lemma isFibredOneMorphism_pullbackUnitPushUniv :
    p.IsFibredOneMorphism (StrictPullback.structureFunctor u (pullbackProj p u))
      (pullbackUnitPushUniv p u) := by
  exact isFibredOneMorphism_liftFib_pullbackUnitLoc p u

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [q.IsFibered] in
/-- **The unit read over `𝒞` is fully faithful** when `u` is: this is
`CategoryTheory.Comma.pullbackUnitLoc_full` and
`CategoryTheory.Comma.pullbackUnitLoc_faithful` transported through the lift. -/
lemma fullyFaithful_pullbackUnitPushUniv :
    (pullbackUnitPushUniv p u).Full ∧ (pullbackUnitPushUniv p u).Faithful := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  have h1 := pullbackUnitLoc_full p u (fun _ => inferInstance)
  have h2 := pullbackUnitLoc_faithful p u (fun _ => inferInstance)
  exact ⟨full_liftFib_univ _, faithful_liftFib_univ _⟩

/-- **The canonical 1-morphism `can : 𝒮 ⟶ f_*f⁻¹𝒮` of Stacks 04WS (1).** It is the image of the
stackification `G : u_p 𝒮 ⥤ f⁻¹𝒮` under the functor `A` of Stacks 04WI, that is
`x ↦ (p(x), G(ι(x)))` where `ι` is the unit `CategoryTheory.Comma.pullbackUnitLoc`. This is the
description the source gives of it. -/
noncomputable def pullbackStackCanUniv : 𝒮 ⥤ StrictPullback u q :=
  (PullbackAdjunction.restrictBased p u q ⟨G, hG.comp_eq⟩).toFunctor

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The base of `can(x)` is `p(x)`. -/
@[simp] lemma pullbackStackCanUniv_obj_base (x : 𝒮) :
    ((pullbackStackCanUniv p u hG).obj x).base = p.obj x := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The fibre component of `can(x)` is `G(ι(x))`. -/
@[simp] lemma pullbackStackCanUniv_obj_fib (x : 𝒮) :
    ((pullbackStackCanUniv p u hG).obj x).fib = G.obj ((pullbackUnitLoc p u).obj x) := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The base of `can(α)` is `p(α)`. -/
@[simp] lemma pullbackStackCanUniv_map_base {x y : 𝒮} (α : x ⟶ y) :
    ((pullbackStackCanUniv p u hG).map α).base = p.map α := rfl

omit [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u] [u.Full] [u.Faithful]
  [q.IsFibered] in
/-- The fibre component of `can(α)` is `G(ι(α))`. -/
@[simp] lemma pullbackStackCanUniv_map_fib {x y : 𝒮} (α : x ⟶ y) :
    ((pullbackStackCanUniv p u hG).map α).fib = G.map ((pullbackUnitLoc p u).map α) := rfl

omit [u.Full] [u.Faithful] [q.IsFibered] in
/-- `can` is a 1-morphism of fibred categories over `𝒞`, by Stacks 04WI. -/
lemma isFibredOneMorphism_pullbackStackCanUniv :
    p.IsFibredOneMorphism (StrictPullback.structureFunctor u q) (pullbackStackCanUniv p u hG) :=
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  PullbackAdjunction.isFibredOneMorphism_restrictBased p u q (fun _ => inferInstance) _ hG

omit [u.IsContinuous J K] [u.Faithful] in
/-- **Local essential surjectivity of `can`**, condition (2) of Stacks 046N for the canonical
1-morphism `𝒮 ⟶ f_*f⁻¹𝒮`.

Let `X` be an object of the fibre of `f_*f⁻¹𝒮` over `U`, that is an object of the fibre of `f⁻¹𝒮`
over `u(U)`. Clause (2) of Stacks 02ZN for the stackification `G` gives a `K`-covering sieve of
`u(U)` along whose members `X` comes from `u_p 𝒮`; cocontinuity of `u` pulls that sieve back to a
`J`-covering sieve of `U`, and along its members the object of `u_p 𝒮` lies over an object in the
image of `u`, hence comes from `𝒮` by
`CategoryTheory.Comma.exists_iso_pullbackUnitLoc` — which is where full faithfulness of `u`
enters. -/
theorem locallyEssSurjOnFibers_pullbackStackCanUniv
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.LocallyEssSurjOnFibers (StrictPullback.isFibered_structureFunctor u q)
      (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq J := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  intro U X
  obtain ⟨R', hR', hess⟩ := hobj (u.obj U) (StrictPullback.fiberFib X)
  refine ⟨R'.functorPullback u, u.cover_lift J K hR', ?_⟩
  intro V a ha
  obtain ⟨Y, ⟨eY⟩⟩ := hess (g := u.map a) ha
  obtain ⟨z, hz, e, he⟩ :=
    exists_iso_pullbackUnitLoc p u (fun _ => inferInstance) Y.1 Y.2
  -- The vertical isomorphism `Y ≅ ι(z)` of the fibre of `u_p 𝒮` over `u(V)`.
  set eι : Y ≅ (⟨(pullbackUnitLoc p u).obj z, by
      rw [pullbackUnitLoc_obj, pullbackProj_obj]
      exact congrArg u.obj hz⟩ : (pullbackProj p u).Fiber (u.obj V)) :=
    Functor.Fiber.isoMk e he with heι
  -- Transport it through `G` and compose with the two given comparisons.
  set ε : StrictPullback.fiberFib
      ((Functor.Fiber.mapOfComp p (StrictPullback.structureFunctor u q)
        (pullbackStackCanUniv p u hG)
          (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq V).obj ⟨z, hz⟩) ≅
      StrictPullback.fiberFib
        (Functor.pullbackFiber (StrictPullback.structureFunctor u q) X a) :=
    (((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj V)).mapIso eι).symm ≪≫ eY) ≪≫
      StrictPullback.fiberFibPullbackIso X a with hε
  exact ⟨⟨z, hz⟩, ⟨fiberIsoOfFibUniv u ε⟩⟩

/-! ### Fibrewise full faithfulness of `can`, in independent universes -/

section FibrewiseCanUniv

variable (hs : p.IsStack J) (hq : q.IsStack K)
  (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))

/-- The object of the fibre of `u_p 𝒮` over `u(U)` attached to an object of the fibre of `𝒮` over
`U` by the unit. -/
noncomputable def unitFiberUniv {U : 𝒞} (x : p.Fiber U) : (pullbackProj p u).Fiber (u.obj U) :=
  ⟨(pullbackUnitLoc p u).obj x.1, by
    rw [pullbackUnitLoc_obj, pullbackProj_obj]
    exact congrArg u.obj x.2⟩

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] hG in
/-- On the fibre over `U`, the fibre component of the image of `x` under `pullbackUnitPushUniv` is
`unitFiberUniv p u x`. -/
lemma fiberFib_unitPushUniv {U : 𝒞} (x : p.Fiber U) :
    StrictPullback.fiberFib ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackUnitPushUniv p u).comp_eq U).obj x) = unitFiberUniv p u x := rfl

omit [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] [q.IsFibered] in
/-- On the fibre over `U`, the fibre component of `can(x)` is the image of `unitFiberUniv p u x`
under the functor induced by `G` on fibres over `u(U)`. -/
lemma fiberFib_canUniv {U : 𝒞} (x : p.Fiber U) :
    StrictPullback.fiberFib ((Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).obj x) =
      (Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiberUniv p u x) := rfl

include hs hq hmor in
/-- **The comparison of morphism presheaves induced by the stackification is bijective on global
sections over `u(U)`, for the objects coming from `𝒮`.**

The presheaf `Mor(ι x, ι y)` on `𝒟/u(U)` restricts along `𝒞/U ⥤ 𝒟/u(U)` to `Mor(x, y)` on `𝒞/U`,
because the unit is a fully faithful 1-morphism over `𝒞` into the pushforward of `u_p 𝒮`; so that
restriction is a sheaf, `𝒮` being a stack. The restriction of `Mor(G ι x, G ι y)` is a sheaf for
the same reason, `f⁻¹𝒮` being a stack and its pushforward therefore a stack (Stacks 04WC). The map
between them is locally bijective, being the restriction along a **cocontinuous** functor of a
locally bijective map (clause (1) of Stacks 02ZN). A locally bijective map of sheaves is an
isomorphism, so it is bijective on sections over the terminal object of `𝒞/U`. -/
theorem bijective_morPresheafMap_unitFiberUniv (U : 𝒞) (x y : p.Fiber U) :
    Function.Bijective ((hG.morPresheafMap (unitFiberUniv p u x) (unitFiberUniv p u y)).app
      (Opposite.op (Over.mk (𝟙 (u.obj U))))) := by
  have hι := isFibredOneMorphism_pullbackUnitPushUniv p u
  obtain ⟨hfull, hfaith⟩ := fullyFaithful_pullbackUnitPushUniv p u
  have := hfull
  have := hfaith
  -- The two presheaves on `𝒞/U`.
  set X := (Functor.fiberFunctorOfCompEq hι.comp_eq U).obj x with hX
  set Y := (Functor.fiberFunctorOfCompEq hι.comp_eq U).obj y with hY
  have hiso : IsIso (hι.morPresheafMapULift x y) :=
    isIso_morPresheafMapULift_of_fullyFaithful hι x y
  have := hiso
  -- Both are sheaves on `𝒞/U`: the morphism presheaves of `𝒮` and of the pushforward of `f⁻¹𝒮`
  -- are, and they are identified with them up to a universe lift.
  have hsh₁ : Presheaf.IsSheaf (J.over U)
      ((Over.post (X := U) u).op ⋙
        Functor.morPresheaf (pullbackProj p u) (unitFiberUniv p u x) (unitFiberUniv p u y)) := by
    have hx0 := hs.isMorSheaf U x y
    rw [Functor.IsMorSheaf, isSheaf_iff_isSheaf_of_type] at hx0
    have hx1 := (isSheaf_iff_isSheaf_of_type _ _).2
      (Presieve.isSheaf_comp_uliftFunctor.{_, max u₂ u₃ vc vd vs} (J := J.over U) hx0)
    have h0 := (Presheaf.isSheaf_of_iso_iff
      (asIso (hι.morPresheafMapULift x y) ≪≫
        Functor.isoWhiskerRight (StrictPullback.morPresheafFibIso X Y) uliftFunctor.{vs})).1 hx1
    rw [isSheaf_iff_isSheaf_of_type] at h0 ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff (J := J.over U) (P := (Over.post (X := U) u).op ⋙
      Functor.morPresheaf (pullbackProj p u) (unitFiberUniv p u x) (unitFiberUniv p u y))).1
      ((Presieve.isSheaf_comp_uliftFunctor_iff (J := J.over U)).1 h0)
  have hsh₂ : Presheaf.IsSheaf (J.over U)
      ((Over.post (X := U) u).op ⋙
        Functor.morPresheaf q ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj
            (unitFiberUniv p u x))
          ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiberUniv p u y))) := by
    have h0 := (Presheaf.isSheaf_of_iso_iff (StrictPullback.morPresheafFibIso
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).obj x)
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).obj y))).1
      (StrictPullback.isMorSheaf_structureFunctor J K u q hq.isMorSheaf U _ _)
    rw [isSheaf_iff_isSheaf_of_type] at h0 ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff (J := J.over U) (P := (Over.post (X := U) u).op ⋙
      Functor.morPresheaf q ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj
          (unitFiberUniv p u x))
        ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).obj (unitFiberUniv p u y)))).1 h0
    -- The restriction of the comparison is locally bijective.
  obtain ⟨hinj, hsurj⟩ := hmor (u.obj U) (unitFiberUniv p u x) (unitFiberUniv p u y)
  have := hinj
  have := hsurj
  exact bijective_app_of_obj_eq _ (congrArg Over.mk (u.map_id U))
    (bijective_app_of_isSheaf_whisker (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) _ hsh₁
      hsh₂ (Over.mk (𝟙 U)))

include hs hq hmor in
/-- **The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is fully faithful on every fibre.** The fibre of
`f_*f⁻¹𝒮` over `U` is the fibre of `f⁻¹𝒮` over `u(U)`, the unit is fully faithful, and the
stackification `G` is bijective on the hom-sets of the objects coming from `𝒮` by
`CategoryTheory.Comma.bijective_morPresheafMap_unitFiberUniv`. -/
theorem bijective_fiber_pullbackStackCanUniv (U : 𝒞) (x y : p.Fiber U) :
    Function.Bijective (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).map m) := by
  have hι := isFibredOneMorphism_pullbackUnitPushUniv p u
  obtain ⟨hfull, hfaith⟩ := fullyFaithful_pullbackUnitPushUniv p u
  have := hfull
  have := hfaith
  have hfl : (Functor.fiberFunctorOfCompEq hι.comp_eq U).Full :=
    Functor.Fiber.full_mapOfComp hι.comp_eq U
  have hfa : (Functor.fiberFunctorOfCompEq hι.comp_eq U).Faithful :=
    Functor.Fiber.faithful_mapOfComp hι.comp_eq U
  have hb1 : Function.Bijective
      (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hι.comp_eq U).map m) :=
    ⟨fun _ _ h => hfa.map_injective h, fun n => hfl.map_surjective n⟩
  have hb2 := bijective_fiberFunctor_map_of_bijective_app hG (unitFiberUniv p u x)
    (unitFiberUniv p u y) (bijective_morPresheafMap_unitFiberUniv p u hG hs hq hmor U x y)
  set e1 := fiberFibHomEquivUniv u ((Functor.fiberFunctorOfCompEq hι.comp_eq U).obj x)
    ((Functor.fiberFunctorOfCompEq hι.comp_eq U).obj y) with he1
  set e2 := fiberFibHomEquivUniv u ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).obj x)
    ((Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).obj y) with he2
  have hcomp : ∀ m : x ⟶ y, (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).map m =
      e2.symm ((Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).map
        (e1 ((Functor.fiberFunctorOfCompEq hι.comp_eq U).map m))) := by
    intro m
    rw [Equiv.eq_symm_apply]
    exact Functor.Fiber.hom_ext rfl
  have hfun : (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq U).map m) =
      e2.symm ∘ ((fun k : unitFiberUniv p u x ⟶ unitFiberUniv p u y =>
          (Functor.fiberFunctorOfCompEq hG.comp_eq (u.obj U)).map k) ∘
        (e1 ∘ (fun m : x ⟶ y => (Functor.fiberFunctorOfCompEq hι.comp_eq U).map m))) :=
    funext hcomp
  rw [hfun]
  exact e2.symm.bijective.comp (hb2.comp (e1.bijective.comp hb1))

include hs hq hmor in
/-- **The canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is fully faithful.** A 1-morphism of fibred
categories which is fully faithful on every fibre is fully faithful. -/
theorem fullyFaithful_pullbackStackCanUniv :
    (pullbackStackCanUniv p u hG).Full ∧ (pullbackStackCanUniv p u hG).Faithful := by
  have hcan := isFibredOneMorphism_pullbackStackCanUniv p u hG
  refine ⟨full_of_fiber_full hcan ?_, faithful_of_fiber_faithful hcan ?_⟩
  · exact fun U => ⟨fun {x y} n =>
      (bijective_fiber_pullbackStackCanUniv p u hG hs hq hmor U x y).surjective n⟩
  · exact fun U => ⟨fun {x y} _ _ h =>
      (bijective_fiber_pullbackStackCanUniv p u hG hs hq hmor U x y).injective h⟩

include hs hq hmor in
/-- **Stacks 04WS (1), for the pullback given by a supplied stackification.** Let `u : 𝒞 ⥤ 𝒟`
satisfy the assumptions of Sites 00XU — continuous, cocontinuous, fully faithful, `𝒞` finitely
complete and `u` left exact — and let `f : 𝒟 ⟶ 𝒞` be the associated morphism of sites. Let `𝒮` be
a stack over `(𝒞, J)` and let `G : u_p 𝒮 ⥤ f⁻¹𝒮` be a stackification of `u_p 𝒮` over `(𝒟, K)` in
the sense of Stacks 02ZN. Then the canonical 1-morphism `𝒮 ⟶ f_*f⁻¹𝒮` is an **equivalence of
stacks over `𝒞`**: a quasi-inverse strictly over `𝒞`, with vertical unit and counit.

By Stacks 046N it suffices that the canonical 1-morphism be fully faithful and that every object
of a fibre of `f_*f⁻¹𝒮` be locally in its essential image on fibres, which are
`CategoryTheory.Comma.fullyFaithful_pullbackStackCanUniv` and
`CategoryTheory.Comma.locallyEssSurjOnFibers_pullbackStackCanUniv`.

The statement is *conditional on being given a stackification*, which Stacks 02ZN supplies once
assembled. -/
theorem isEquivalenceOver_pullbackStackCanUniv
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Nonempty (Functor.IsEquivalenceOver p (StrictPullback.structureFunctor u q)
      (pullbackStackCanUniv p u hG)) := by
  obtain ⟨hfl, hfa⟩ := fullyFaithful_pullbackStackCanUniv p u hG hs hq hmor
  have := hfl
  have := hfa
  exact (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers hs
    (StrictPullback.isStack_structureFunctor J K u q hq)
    (isFibredOneMorphism_pullbackStackCanUniv p u hG)).2
    (locallyEssSurjOnFibers_pullbackStackCanUniv p u hG hobj)

include hs hq hmor in
/-- The vertical preimages produced by Stacks 04WS (1): every object of `f_*f⁻¹𝒮` is isomorphic,
over an identity of `𝒞`, to the image of an object of `𝒮`. -/
theorem hasVerticalPreimages_pullbackStackCanUniv
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.HasVerticalPreimages p (StrictPullback.structureFunctor u q)
      (pullbackStackCanUniv p u hG) := by
  obtain ⟨E⟩ := isEquivalenceOver_pullbackStackCanUniv p u hG hs hq hmor hobj
  intro y
  have hF := (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq
  obtain ⟨x, e, he⟩ := exists_vertical_iso_of_isEquivalenceOver E hF y
  have := he
  exact ⟨x, (Functor.congr_obj hF x).symm.trans
    (IsHomLift.domain_eq (StrictPullback.structureFunctor u q) (𝟙 _) e.hom), e.symm,
    IsHomLift.lift_id_inv (StrictPullback.structureFunctor u q) _ e⟩

include hs hq hmor in
/-- **Stacks 04WS (1), as data, in independent universes.** Let `u : 𝒞 ⥤ 𝒟` satisfy the assumptions
of Sites 00XU — continuous, cocontinuous, fully faithful, `𝒞` finitely complete and `u` left exact
— and let `f : 𝒟 ⟶ 𝒞` be the associated morphism of sites. Let `𝒮` be a stack over `(𝒞, J)` and let
`G : u_p 𝒮 ⥤ f⁻¹𝒮` exhibit `f⁻¹𝒮` as the stackification of `u_p 𝒮` over `(𝒟, K)` in the sense of
Stacks 02ZN. Then the canonical functor `𝒮 ⟶ f_*f⁻¹𝒮` is an **equivalence of stacks over `𝒞`**: a
quasi-inverse strictly over `𝒞`, together with vertical unit and counit isomorphisms.

By Stacks 046N it suffices that the canonical functor be fully faithful and that every object of a
fibre of `f_*f⁻¹𝒮` be locally in its essential image on fibres, which are
`CategoryTheory.Comma.fullyFaithful_pullbackStackCanUniv` and
`CategoryTheory.Comma.locallyEssSurjOnFibers_pullbackStackCanUniv`.

The statement is *conditional on being given a stackification*, which Stacks 02ZN supplies once
assembled. -/
noncomputable def equivalenceOverPullbackStackCanUniv
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g)) :
    Functor.IsEquivalenceOver p (StrictPullback.structureFunctor u q)
      (pullbackStackCanUniv p u hG) :=
  haveI := (fullyFaithful_pullbackStackCanUniv p u hG hs hq hmor).1
  haveI := (fullyFaithful_pullbackStackCanUniv p u hG hs hq hmor).2
  Functor.isEquivalenceOver_of_exists_vertical_iso
    (isFibredOneMorphism_pullbackStackCanUniv p u hG).comp_eq
    (hasVerticalPreimages_pullbackStackCanUniv p u hG hs hq hmor hobj)

end FibrewiseCanUniv

end CanonicalUniv

/-! ### Stacks 04WS (2): the equivalence of morphism categories, in independent universes -/

section MorphismCategoriesUniv

universe vc vd vs u₄ u₅

open Limits

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂} [Category.{vd} 𝒟]
  {𝒮 : Type u₃} [Category.{vs} 𝒮] {𝒮₂ : Type u₃} [Category.{vs} 𝒮₂]
  {𝒳 : Type u₄} [Category.{max u₂ u₃ vd vs} 𝒳] {𝒳₂ : Type u₅} [Category.{max u₂ u₃ vd vs} 𝒳₂]
  {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟}
  (p : 𝒮 ⥤ 𝒞) (p₂ : 𝒮₂ ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [p₂.IsFibered]
  [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)
  {q₂ : 𝒳₂ ⥤ 𝒟} [q₂.IsFibered] {G₂ : pullbackLocalization p₂ u ⥤ 𝒳₂}
  (hG₂ : (pullbackProj p₂ u).IsFibredOneMorphism q₂ G₂)
  (hs : p.IsStack J) (hq : q.IsStack K)
  (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))
  (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
    (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g))
  (hs₂ : p₂.IsStack J) (hq₂ : q₂.IsStack K)
  (hmor₂ : ∀ (V : 𝒟) (a b : (pullbackProj p₂ u).Fiber V),
    Presheaf.IsLocallyInjective (K.over V) (hG₂.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (K.over V) (hG₂.morPresheafMap a b))
  (hobj₂ : ∀ (V : 𝒟) (x' : q₂.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
    (Functor.fiberFunctorOfCompEq hG₂.comp_eq W).essImage (Functor.pullbackFiber q₂ x' g))

include hs₂ hq₂ hmor₂ hobj₂ in
/-- The canonical 1-morphism `𝒮₂ ⟶ f_*f⁻¹𝒮₂` is an **equivalence in the 2-category of fibred
categories over `𝒞`**: by Stacks 04WS (1) it is an equivalence over `𝒞`, and
`CategoryTheory.Functor.isFibredEquivalenceOver_of_fullyFaithful` upgrades that to a quasi-inverse
which is again a 1-morphism of fibred categories. -/
theorem isFibredEquivalenceOver_pullbackStackCanUniv :
    Functor.IsFibredEquivalenceOver p₂ (StrictPullback.structureFunctor u q₂)
      (pullbackStackCanUniv p₂ u hG₂) := by
  obtain ⟨E⟩ := isEquivalenceOver_pullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂ hobj₂
  obtain ⟨hfl, hfa⟩ := fullyFaithful_pullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂
  have := hfl
  have := hfa
  have hKc := isFibredOneMorphism_pullbackStackCanUniv p₂ u hG₂
  have hsurj := exists_vertical_iso_of_isEquivalenceOver E hKc.comp_eq
  have h := Functor.isFibredEquivalenceOver_of_fullyFaithful
    (q := StrictPullback.structureFunctor u q₂) (pullbackStackCanUniv p₂ u hG₂) hsurj
  rwa [hKc.comp_eq] at h

include hs hq hmor hobj hs₂ hq₂ hmor₂ hobj₂ in
/-- **Stacks 04WS (2), for the pullbacks given by supplied stackifications, in independent
universes.** Let `u : 𝒞 ⥤ 𝒟` satisfy the assumptions of Sites 00XU and let `f : 𝒟 ⟶ 𝒞` be the
associated morphism of sites. For stacks `𝒮` and `𝒮₂` over `(𝒞, J)` with pullbacks `f⁻¹𝒮` and
`f⁻¹𝒮₂` given by supplied stackifications of `u_p 𝒮` and `u_p 𝒮₂` (Stacks 04WJ), the morphism
categories

`Mor_{Stacks/𝒞}(𝒮, 𝒮₂)`  and  `Mor_{Stacks/𝒟}(f⁻¹𝒮, f⁻¹𝒮₂)`

are canonically equivalent. The equivalence is the composite of post-composition with the canonical
equivalence `𝒮₂ ⟶ f_*f⁻¹𝒮₂` of clause (1) with the adjunction of Stacks 04WK at `𝒯 = f⁻¹𝒮₂`; the
direction `f⁻¹` is its quasi-inverse.

Both clauses are conditional on being given stackifications, which Stacks 02ZN supplies once
assembled. -/
noncomputable def equivalenceFibredMorPullbackStackUniv :
    Functor.FibredMor p p₂ ≌
      Functor.FibredMor q q₂ :=
  haveI : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  have hfe := isFibredEquivalenceOver_pullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂ hobj₂
  have hff := fullyFaithful_pullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂
  haveI := hff.1
  haveI := hff.2
  (postcompFibredMorEquivalenceUniv (p := p) hfe.isFibredOneMorphism
      hfe.exists_inverse.choose_spec.choose
      hfe.exists_inverse.choose_spec.choose_spec.choose_spec.choose_spec.choose
      hfe.exists_inverse.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec).trans
    (Functor.equivalenceFibredMorPushforwardPullbackStackUniv J K p u hs hq hG hmor hobj hq₂)

end MorphismCategoriesUniv

end Comma

end CategoryTheory

end
