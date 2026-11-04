module

public import
  StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreReduction
public import
  StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.UnitPushforwardFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# A contraction near a fibre, universally (the scheme case of Stacks 0E88)

Let `f : X ⟶ Y` be a proper morphism of schemes over `q : Y ⟶ U`, with `X` flat and locally of
finite presentation over `U`, `q` proper and locally of finite presentation, and let `u` be a
point of `U`. If on the fibre over `u` the morphism `f_u : X_u ⟶ Y_u` has fibres of dimension
at most one, `R¹f_{u,*}𝒪_{X_u} = 0` and `𝒪_{Y_u} ⟶ f_{u,*}𝒪_{X_u}` is an isomorphism, then there
is an open neighbourhood `N` of `u` such that, for every morphism `T ⟶ U` landing in `N`, the base
change `f_T : X_T ⟶ Y_T` satisfies `𝒪_{Y_T} = f_{T,*}𝒪_{X_T}` and `R¹f_{T,*}𝒪_{X_T} = 0`.

This is the scheme case of Stacks 0E88. Stacks 0E7L, in the namespace
`Stacks.AlgebraicGeometry.TopDegreeBaseChange` as
`exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre`, gives an open `V ⊇ Y_u` of `Y` over
which the conclusions hold universally. Since `q` is proper, hence closed, the points of `U` whose
fibre lies in `V` form an open neighbourhood of `u`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_isOpen_forall_isPullback_of_specialFibre`.

## Implementation notes

The statement involves no derived category: its conclusion is Mathlib's `ℕ`-indexed right derived
functor. The local instance `HasDerivedCategory.standard` is only there to consume Stacks 0E7L,
which is stated with the `ℤ`-indexed form `CategoryTheory.Functor.rightDerivedPlus` in that model.

The base changes are quantified over all cartesian squares, so that the statement can be applied
to base changes that are not the chosen fibre products. The conclusions are transported from the
chosen fibre products of Stacks 0E7L along isomorphisms, as flat base changes.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry.C1590Private

universe u

variable {X Y U : Scheme.{u}}

/-- Given a cartesian square `t` with right edge `f`, a cartesian square over `f` whose bottom edge
factors through `t` is the pasting of `t` with a cartesian square on the left. -/
theorem isPullback_lift_of_isPullback_comp {C : Type*} [Category C] {P A B Z A' B' : C}
    {a : P ⟶ A} {b : P ⟶ Z} {f : A ⟶ B} {c : Z ⟶ B} (t : IsPullback a b f c) {iX : A' ⟶ A}
    {f' : A' ⟶ B'} {g : B' ⟶ Z} (hX : IsPullback iX f' f (g ≫ c)) :
    IsPullback (t.lift iX (f' ≫ g) (by rw [hX.w, Category.assoc])) f' b g :=
  IsPullback.of_right (by rwa [t.lift_fst]) (t.lift_snd _ _ _) t

/-- Restricting a cartesian square `IsPullback iY qY q h` to an open `V` of `Y` containing the
range of `iY` gives a cartesian square over `V.ι ≫ q`. -/
theorem isPullback_lift_opensι_of_range_subset {Y' T : Scheme.{u}} {q : Y ⟶ U} {h : T ⟶ U}
    {iY : Y' ⟶ Y} {qY : Y' ⟶ T} (hY : IsPullback iY qY q h) (V : Y.Opens)
    (hsub : Set.range iY ⊆ Set.range V.ι) :
    IsPullback (IsOpenImmersion.lift V.ι iY hsub) qY (V.ι ≫ q) h := by
  have hiYV : IsOpenImmersion.lift V.ι iY hsub ≫ V.ι = iY := IsOpenImmersion.lift_fac _ _ _
  refine IsPullback.of_isLimit' ⟨by rw [← Category.assoc, hiYV, hY.w]⟩
    (PullbackCone.IsLimit.mk _ (fun s => hY.lift (s.fst ≫ V.ι) s.snd
      (by rw [Category.assoc, s.condition])) (fun s => ?_) (fun s => hY.lift_snd _ _ _)
      (fun s m h₁ h₂ => ?_))
  · rw [← cancel_mono V.ι, Category.assoc, hiYV, hY.lift_fst]
  · apply hY.hom_ext
    · rw [hY.lift_fst, ← hiYV, ← Category.assoc, h₁]
    · rw [hY.lift_snd, h₂]

/-- **The scheme case of Stacks 0E88.** Let `f : X ⟶ Y` be proper over `q : Y ⟶ U`, with
`f ≫ q` flat and locally of finite presentation and `q` proper and locally of finite
presentation. If at a point `u` of `U` the fibres of `f_u` have dimension at most one,
`R¹f_{u,*}𝒪 = 0` and `𝒪 ⟶ f_{u,*}𝒪` is an isomorphism, then there is an open neighbourhood `N`
of `u` such that every base change `f' : X' ⟶ Y'` of `f` along a morphism `T ⟶ U` landing in `N`
has `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` an isomorphism and `R¹f'_*𝒪_{X'} = 0`. -/
theorem exists_isOpen_forall_isPullback_of_specialFibre (f : X ⟶ Y) (q : Y ⟶ U) (u : U)
    [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q] [IsProper f]
    [IsProper q] [Flat (f ≫ q)]
    (hdim : ∀ y : q.fiber u, topologicalKrullDim ((Stacks.Flatness.fiberHom f q u).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι u))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι u)))) :
    ∃ N : U.Opens, u ∈ N ∧ ∀ ⦃T Y' X' : Scheme.{u}⦄ (h : T ⟶ U) (iY : Y' ⟶ Y) (qY : Y' ⟶ T)
      (iX : X' ⟶ X) (f' : X' ⟶ Y'), Set.range h ⊆ N → IsPullback iY qY q h →
      IsPullback iX f' f iY →
      IsIso (Scheme.Modules.unitToPushforwardUnit f') ∧
        IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
          (SheafOfModules.unit X'.ringCatSheaf)) := by
  obtain ⟨V, hV, -, -, -, -, -, hbc⟩ :=
    exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre f q u
      (fun x _ => isFlatAt_of_flat_comp_ι (f ≫ q) (U := ⊤) inferInstance (Set.mem_univ x))
      hdim hR hiso
  let N : U.Opens :=
    ⟨(q.base '' (V : Set Y)ᶜ)ᶜ, (q.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨N, ?_, ?_⟩
  · rintro ⟨y, hy, hyu⟩
    exact hy (hV y hyu)
  intro T Y' X' h iY qY iX f' hN hY hX
  have hsub : Set.range iY ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y', rfl⟩
    by_contra hy
    exact hN ⟨qY y', rfl⟩ ⟨iY y', hy, by rw [← Scheme.Hom.comp_apply, hY.w, Scheme.Hom.comp_apply]⟩
  have hYV := isPullback_lift_opensι_of_range_subset hY V hsub
  let g : Y' ⟶ pullback (V.ι ≫ q) h := hYV.isoPullback.hom
  let f₀ := pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h)
  obtain ⟨-, -, -, hR₀, hiso₀⟩ := hbc h
  have t : IsPullback (pullback.fst (f ∣_ V) (pullback.fst (V.ι ≫ q) h) ≫ (f ⁻¹ᵁ V).ι) f₀ f
      (pullback.fst (V.ι ≫ q) h ≫ V.ι) :=
    (IsPullback.of_hasPullback (f ∣_ V) (pullback.fst (V.ι ≫ q) h)).paste_horiz
      (isPullback_morphismRestrict f V).flip
  have hX' : IsPullback iX f' f (g ≫ pullback.fst (V.ι ≫ q) h ≫ V.ι) := by
    rwa [← Category.assoc, hYV.isoPullback_hom_fst, IsOpenImmersion.lift_fac]
  have hgX := isPullback_lift_of_isPullback_comp t hX'
  have : IsProper (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance
  have : Flat g := inferInstance
  refine ⟨Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isPullback f₀ hgX hiso₀, ?_⟩
  open Stacks.AlgebraicGeometry.FlatBaseChangeDerived in
  exact isZero_rightDerived_pushforward_unit_of_isPullback
    hgX 1 ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2 hR₀)

/-- A fibre of a morphism embeds in its source, so its dimension is at most that of the source. -/
private theorem topologicalKrullDim_fiber_le {A B : Scheme.{u}} (g : A ⟶ B) (b : B) {n : WithBot ℕ∞}
    (h : topologicalKrullDim A ≤ n) : topologicalKrullDim (g.fiber b) ≤ n :=
  (Topology.IsInducing.topologicalKrullDim_le (g.fiberι b).isEmbedding.isInducing).trans h

/-- A fibre of the morphism of fibres `(f ≫ q)_u ⟶ q_u` embeds in `(f ≫ q)_u`, so its dimension is
at most that of `(f ≫ q)_u`. -/
theorem topologicalKrullDim_fiber_fiberHom_le' (f : X ⟶ Y) (q : Y ⟶ U) (u : U)
    {n : WithBot ℕ∞} (h : topologicalKrullDim ((f ≫ q).fiber u) ≤ n)
    (y : q.fiber u) : topologicalKrullDim ((Stacks.Flatness.fiberHom f q u).fiber y) ≤ n :=
  topologicalKrullDim_fiber_le _ y h

/-- **The scheme case of Stacks 0E88, with the fibre given by any cartesian square.** As
`AlgebraicGeometry.C1590Private.exists_isOpen_forall_isPullback_of_specialFibre`, with the
hypotheses on the fibre over `u` read on an arbitrary cartesian presentation
`f_u : X_u ⟶ Y_u` of it over `Spec κ(u)`, and the fibre dimension bounded by the dimension of
`X_u`. -/
theorem exists_isOpen_forall_isPullback_of_fibre (f : X ⟶ Y) (q : Y ⟶ U) (u : U)
    [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q] [IsProper f]
    [IsProper q] [Flat (f ≫ q)] {Fx Fy : Scheme.{u}} (iy : Fy ⟶ Y)
    (py : Fy ⟶ Spec (U.residueField u)) (ix : Fx ⟶ X) (fF : Fx ⟶ Fy)
    (hy : IsPullback iy py q (U.fromSpecResidueField u)) (hx : IsPullback ix fF f iy)
    (hdim : topologicalKrullDim Fx ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf fF))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit fF)) :
    ∃ N : U.Opens, u ∈ N ∧ ∀ ⦃T Y' X' : Scheme.{u}⦄ (h : T ⟶ U) (iY : Y' ⟶ Y) (qY : Y' ⟶ T)
      (iX : X' ⟶ X) (f' : X' ⟶ Y'), Set.range h ⊆ N → IsPullback iY qY q h →
      IsPullback iX f' f iY →
      IsIso (Scheme.Modules.unitToPushforwardUnit f') ∧
        IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
          (SheafOfModules.unit X'.ringCatSheaf)) := by
  -- the fibre of `f ≫ q` over `u` is `Fx`
  have hdimX : topologicalKrullDim ((f ≫ q).fiber u) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    (Topology.IsInducing.topologicalKrullDim_le
      (Scheme.Hom.homeomorph (hx.paste_vert hy).isoPullback.inv).isInducing).trans hdim
  -- the chosen presentation of the fibre of `q`
  let eY : Fy ≅ q.fiber u := hy.isoPullback
  have t := IsPullback.of_hasPullback f (q.fiberι u)
  have heY : eY.hom ≫ q.fiberι u = iy := hy.isoPullback_hom_fst
  have hx' : IsPullback ix fF f (eY.hom ≫ q.fiberι u) := by rwa [heY]
  let gX : Fx ⟶ pullback f (q.fiberι u) :=
    t.lift ix (fF ≫ eY.hom) (by rw [hx'.w, Category.assoc])
  have hgX : IsPullback gX fF (pullback.snd f (q.fiberι u)) eY.hom :=
    isPullback_lift_of_isPullback_comp t hx'
  have : IsProper fF := MorphismProperty.of_isPullback hx inferInstance
  have hdimF : ∀ y : Fy, topologicalKrullDim (fF.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    fun y => topologicalKrullDim_fiber_le fF y hdim
  have : IsIso gX := hgX.isIso_fst_of_isIso
  have hgX' : IsPullback (inv gX) (pullback.snd f (q.fiberι u)) fF eY.inv := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, ← Category.assoc, hgX.w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  obtain ⟨hR', hiso'⟩ := isZero_and_isIso_of_isPullback hgX' hdimF hR hiso
  exact exists_isOpen_forall_isPullback_of_specialFibre f q u
    (topologicalKrullDim_fiber_fiberHom_le' f q u hdimX) hR' hiso'

end AlgebraicGeometry.C1590Private

end
