module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.StageDiagram
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Noetherian models of smooth proper families of curves

Let `f : X ⟶ S` be a proper smooth morphism with geometrically connected fibres of dimension at
most one, over an affine scheme `S` on which a given integer `ℓ` is invertible. Writing
`Γ(S, ⊤)` as the union of its subrings of finite type over `ℤ`, the morphism `f` is the base
change of a proper smooth morphism with geometrically connected fibres of dimension at most one
over a Noetherian scheme on which `ℓ` is invertible. This is the reduction to a Noetherian base in
the proof of [Stacks, Tag 0GKV], resting on [Stacks, Tags 01ZM, 081F, 0C0C] and the descent of
geometric connectedness and of the fibre dimension to a stage.

## Main results

* `AlgebraicGeometry.exists_isPullback_stage_of_isProper_of_smooth`: a smooth proper morphism
  over a cofiltered limit of affine schemes is the base change of a smooth proper morphism over a
  stage, carrying along any further property which descends to the stages.
* `AlgebraicGeometry.exists_isPullback_noetherian_of_isProper_of_smooth_of_isUnit`: the
  Noetherian model of a family of curves.
* `AlgebraicGeometry.isProper_smooth_geometricallyConnected_fiber_le_of_isPullback`: the four
  hypotheses on `f` pass to every base change.

## Implementation notes

The limit presentation is `AlgebraicGeometry.affineStageCone`, the spectra of the subrings of
`Γ(S, ⊤)` generated over `ℤ` by finite subsets; the descent of the four properties to a stage is
`AlgebraicGeometry.exists_stage_smooth_proper`, with the fibrewise conditions on a family of
curves supplied by `AlgebraicGeometry.exists_stage_geometricallyConnected_fiber_le`. A stage
whose generators contain an inverse of `ℓ` has `ℓ` invertible.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open LimitStages

/-- **The hypotheses of [Stacks, Tag 0GKV] pass to base changes.** In a cartesian square
`IsPullback g' f' f g`, if `f` is proper and smooth with geometrically connected fibres of
dimension at most one, so is `f'`. -/
@[sga "6 X 7.13.3" "special case"]
theorem isProper_smooth_geometricallyConnected_fiber_le_of_isPullback {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g)
    [IsProper f] [Smooth f] [GeometricallyConnected f] {d : WithBot ℕ∞}
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) :
    IsProper f' ∧ Smooth f' ∧ GeometricallyConnected f' ∧
      ∀ s : S', topologicalKrullDim (f'.fiber s) ≤ d :=
  ⟨MorphismProperty.of_isPullback sq ‹IsProper f›,
    MorphismProperty.of_isPullback sq ‹Smooth f›,
    MorphismProperty.of_isPullback sq ‹GeometricallyConnected f›,
    forall_topologicalKrullDim_fiber_le_of_isPullback sq hd⟩

/-- An integer invertible in a commutative ring `R` is invertible in the subring generated over
`ℤ` by any finite subset of `R` containing an inverse of it, read as global sections of the
spectrum of that subring. -/
theorem isUnit_natCast_specAdjoinFinsetDiagram_obj {R : Type u} [CommRing R] (ℓ : ℕ) (v : R)
    (hv : (ℓ : R) * v = 1) (i : (Finset R)ᵒᵖ) (hi : v ∈ (i.unop : Finset R)) :
    IsUnit (ℓ : Γ((specAdjoinFinsetDiagram R).obj i, ⊤)) := by
  let A := Algebra.adjoin ℤ ((i.unop : Finset R) : Set R)
  have hA : IsUnit (ℓ : A) := by
    refine isUnit_iff_exists.2 ⟨⟨v, Algebra.subset_adjoin hi⟩, ?_, ?_⟩ <;>
      apply Subtype.ext <;> simp [hv, mul_comm]
  have := hA.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rwa [map_natCast] at this

/-- An identification of the base change of `G : A ⟶ B` along `π : S ⟶ T` with
`Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 S)` exhibits `f` as the base change of `G.left`, along a
morphism `S ⟶ B.left` lifting `π`. -/
theorem isPullback_of_overPullback_iso {S T X : Scheme.{u}} (π : S ⟶ T) {A B : Over T}
    (G : A ⟶ B) (f : X ⟶ S) (Φ : (Over.pullback π).obj A ≅ Over.mk f)
    (Ψ : (Over.pullback π).obj B ≅ Over.mk (𝟙 S))
    (h : Φ.hom ≫ (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 S)) =
      (Over.pullback π).map G ≫ Ψ.hom) :
    IsPullback (Φ.inv.left ≫ pullback.fst A.hom π) f G.left (Ψ.inv.left ≫ pullback.fst B.hom π) ∧
      (Ψ.inv.left ≫ pullback.fst B.hom π) ≫ B.hom = π := by
  have h' : Φ.inv ≫ (Over.pullback π).map G = Over.homMk f (by simp) ≫ Ψ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso Φ.inv.left := (Over.forget _).map_isIso Φ.inv
  have : IsIso Ψ.inv.left := (Over.forget _).map_isIso Ψ.inv
  have hsq : Φ.inv.left ≫ ((Over.pullback π).map G).left = f ≫ Ψ.inv.left :=
    congrArg (fun φ ↦ φ.left) h'
  have hw : Ψ.inv.left ≫ pullback.snd B.hom π = 𝟙 S := Over.w Ψ.inv
  refine ⟨(IsPullback.of_horiz_isIso ⟨hsq⟩ :
    IsPullback Φ.inv.left f ((Over.pullback π).map G).left Ψ.inv.left).paste_horiz
      (overPullback_isPullback π A B G), ?_⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hw]
  exact Category.id_comp _

/-- **A smooth proper morphism over a limit of affine schemes comes from a stage.** Let
`S = lim Sᵢ` be a cofiltered limit of affine schemes with affine transition morphisms, and let
`f : X ⟶ S` be proper and smooth. Given a condition `Q` on stages satisfied below every stage,
there are a stage `i` satisfying `Q` and a proper smooth morphism `F : Y ⟶ T`, with `T`
identified with `Sᵢ` by an isomorphism `t` compatible with the projection `S ⟶ Sᵢ`, of which `f`
is the base change along some `g : S ⟶ T`.

A further property `P` of `f`, respecting isomorphisms, is inherited by `F` as soon as it holds at
all sufficiently late stages for every model at a stage of a smooth morphism with the property
(hypothesis `hP`). Taking `P = ⊤` imposes nothing; for a family of curves `P` is geometric
connectedness together with a bound on the dimension of the fibres, and `hP` is
`AlgebraicGeometry.exists_stage_geometricallyConnected_fiber_le`. -/
theorem exists_isPullback_stage_of_isProper_of_smooth {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : ∀ (k : I) (A B : Over (D.obj k)) (_ : FinitePresentation A.hom)
      (_ : FinitePresentation B.hom) [IsAffineHom B.hom]
      (m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B),
      Smooth m.left → P m.left → ∀ (j : I) (e : j ⟶ k)
      (G : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj B),
      (limitIso D c e A).hom ≫ m = (Over.pullback (c.π.app j)).map G ≫ (limitIso D c e B).hom →
      ∃ (j' : I) (g' : j' ⟶ j), ∀ (k' : I) (g'' : k' ⟶ j'),
        P ((Over.pullback (D.map (g'' ≫ g'))).map G).left)
    (Q : I → Prop) (hQ : ∀ i, ∃ (i' : I) (_ : i' ⟶ i), Q i')
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] [Smooth f] (hf : P f) :
    ∃ (i : I), Q i ∧ ∃ (Y T : Scheme.{u}) (F : Y ⟶ T) (g : c.pt ⟶ T) (g' : X ⟶ Y)
      (t : T ⟶ D.obj i), IsIso t ∧ IsProper F ∧ Smooth F ∧ P F ∧
      IsPullback g' f F g ∧ g ≫ t = c.π.app i := by
  have : EssentiallySmall.{u} I := essentiallySmallSelf.{u} I
  have : ∀ i, CompactSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun _ ↦ inferInstance
  obtain ⟨k, A, hA, ⟨eX⟩⟩ := LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
    D c hc (Over.mk f) (⟨inferInstance, inferInstance, inferInstance⟩ : FinitePresentation f)
  let B : Over (D.obj k) := Over.mk (𝟙 (D.obj k))
  have hB : FinitePresentation B.hom := ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 _)),
    inferInstanceAs (QuasiCompact (𝟙 _)), inferInstanceAs (QuasiSeparated (𝟙 _))⟩
  have : IsAffineHom B.hom := inferInstanceAs (IsAffineHom (𝟙 _))
  have : IsIso ((Over.pullback (c.π.app k)).obj B).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (D.obj k)) (c.π.app k)))
  let eS : Over.mk (𝟙 c.pt) ≅ (Over.pullback (c.π.app k)).obj B :=
    Over.isoMk (asIso ((Over.pullback (c.π.app k)).obj B).hom).symm
      (asIso ((Over.pullback (c.π.app k)).obj B).hom).inv_hom_id
  let fo : Over.mk f ⟶ Over.mk (𝟙 c.pt) := Over.homMk f (by simp)
  let m : (Over.pullback (c.π.app k)).obj A ⟶ (Over.pullback (c.π.app k)).obj B :=
    eX.inv ≫ fo ≫ eS.hom
  have hsmRI : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hprRI : MorphismProperty.RespectsIso (@IsProper.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hms : Smooth m.left := (prop_left_conj_iff _ eX.symm fo eS).2 ‹Smooth f›
  have hmp : IsProper m.left := (prop_left_conj_iff _ eX.symm fo eS).2 ‹IsProper f›
  have hmP : P m.left := (prop_left_conj_iff P eX.symm fo eS).2 hf
  obtain ⟨j, e, G, hG, j', g', hall⟩ :=
    exists_stage_smooth_proper D c hc k A B hA hB m hms hmp P (hP k A B hA hB m hms hmP)
  obtain ⟨k', a, hk'⟩ := hQ j'
  let w : k' ⟶ j := a ≫ g'
  let A' := (Over.pullback (D.map e)).obj A
  let B' := (Over.pullback (D.map e)).obj B
  let Ak := (Over.pullback (D.map w)).obj A'
  let Bk := (Over.pullback (D.map w)).obj B'
  let Gk : Ak ⟶ Bk := (Over.pullback (D.map w)).map G
  -- The target of the model is the stage itself.
  have : IsIso B'.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 (D.obj k)) (D.map e)))
  have : IsIso Bk.hom := inferInstanceAs (IsIso (pullback.snd B'.hom (D.map w)))
  -- The cartesian square.
  have N1 : (limitIso D c w A').hom ≫ (Over.pullback (c.π.app j)).map G =
      (Over.pullback (c.π.app k')).map Gk ≫ (limitIso D c w B').hom :=
    overPullbackCompIso_naturality _ _ _ _ G
  let Φ : (Over.pullback (c.π.app k')).obj Ak ≅ Over.mk f :=
    limitIso D c w A' ≪≫ limitIso D c e A ≪≫ eX.symm
  let Ψ : (Over.pullback (c.π.app k')).obj Bk ≅ Over.mk (𝟙 c.pt) :=
    limitIso D c w B' ≪≫ limitIso D c e B ≪≫ eS.symm
  refine ⟨k', hk', Ak.left, Bk.left, Gk.left, Ψ.inv.left ≫ pullback.fst Bk.hom (c.π.app k'),
    Φ.inv.left ≫ pullback.fst Ak.hom (c.π.app k'), Bk.hom, inferInstance, (hall k' a).2.1,
    (hall k' a).1, (hall k' a).2.2, isPullback_of_overPullback_iso (c.π.app k') Gk f Φ Ψ ?_⟩
  change ((limitIso D c w A').hom ≫ (limitIso D c e A).hom ≫ eX.inv) ≫ fo =
    (Over.pullback (c.π.app k')).map Gk ≫
      (limitIso D c w B').hom ≫ (limitIso D c e B).hom ≫ eS.inv
  rw [Category.assoc, Category.assoc, ← reassoc_of% N1, ← reassoc_of% hG]
  simp only [m, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A Noetherian model of a smooth proper family of curves on which `ℓ` is invertible.** Let
`f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most one,
`S` affine, and `ℓ` an integer invertible on `S`. Then there are a proper smooth morphism
`F : Y ⟶ T` with geometrically connected fibres of dimension at most one, `T` locally Noetherian
with `ℓ` invertible on `T`, and a cartesian square `IsPullback g' f F g` exhibiting `f` as the base
change of `F` along `g : S ⟶ T`: write `Γ(S, ⊤)` as the union of its subrings of finite type over
`ℤ` and take one containing an inverse of `ℓ`. -/
theorem exists_isPullback_noetherian_of_isProper_of_smooth_of_isUnit {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) (ℓ : ℕ)
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    ∃ (Y T : Scheme.{u}) (F : Y ⟶ T) (g : S ⟶ T) (g' : X ⟶ Y),
      IsLocallyNoetherian T ∧ IsProper F ∧ Smooth F ∧ GeometricallyConnected F ∧
      (∀ t : T, topologicalKrullDim (F.fiber t) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsUnit (ℓ : Γ(T, ⊤)) ∧ IsPullback g' f F g := by
  let R := Γ(S, ⊤)
  obtain ⟨v, hv⟩ : ∃ v : R, (ℓ : R) * v = 1 := ⟨((hℓ.unit⁻¹ : Rˣ) : R), hℓ.mul_val_inv⟩
  have hQ : ∀ i : (Finset R)ᵒᵖ, ∃ (i' : (Finset R)ᵒᵖ) (_ : i' ⟶ i),
      IsUnit (ℓ : Γ((specAdjoinFinsetDiagram R).obj i', ⊤)) := fun i ↦ by
    obtain ⟨i', a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i (op ({v} : Finset R))
    exact ⟨i', a, isUnit_natCast_specAdjoinFinsetDiagram_obj ℓ v hv i'
      ((leOfHom b.unop) (Finset.mem_singleton_self v))⟩
  let f₀ : X ⟶ (affineStageCone S).pt := f
  have : IsProper f₀ := ‹IsProper f›
  have : Smooth f₀ := ‹Smooth f›
  have : GeometricallyConnected f₀ := ‹GeometricallyConnected f›
  let P : MorphismProperty Scheme.{u} := fun _ _ q => LocallyOfFiniteType q ∧
    GeometricallyConnected q ∧ ∀ s, topologicalKrullDim (q.fiber s) ≤ 1
  have hgcRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlftRI : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : P.RespectsIso := by
    refine MorphismProperty.RespectsIso.mk _ (fun e q ⟨h₁, h₂, h₃⟩ ↦ ?_)
      (fun e q ⟨h₁, h₂, h₃⟩ ↦ ?_)
    · have := h₁
      exact ⟨(MorphismProperty.cancel_left_of_respectsIso _ e.hom q).2 h₁,
        (MorphismProperty.cancel_left_of_respectsIso _ e.hom q).2 h₂,
        forall_topologicalKrullDim_fiber_le_of_isPullback
          (IsPullback.of_horiz_isIso ⟨by simp⟩ :
            IsPullback e.hom (e.hom ≫ q) q (𝟙 _)) h₃⟩
    · have := h₁
      exact ⟨(MorphismProperty.cancel_right_of_respectsIso _ q e.hom).2 h₁,
        (MorphismProperty.cancel_right_of_respectsIso _ q e.hom).2 h₂,
        forall_topologicalKrullDim_fiber_le_of_isPullback
          (IsPullback.of_horiz_isIso ⟨by simp⟩ :
            IsPullback (𝟙 _) (q ≫ e.hom) q e.inv) h₃⟩
  obtain ⟨i, hi, Y, T, F, g, g', t, ht, hFp, hFs, ⟨-, hFg, hFd⟩, hsq, -⟩ :=
    exists_isPullback_stage_of_isProper_of_smooth (specAdjoinFinsetDiagram R)
      (affineStageCone S) (isLimit_affineStageCone S) P
      (fun k A B hA hB _ m hs hm ↦ exists_stage_geometricallyConnected_fiber_le _
        (affineStageCone S) (isLimit_affineStageCone S) k A B hA hB m hs hm.2.1 hm.2.2) _ hQ f₀
      ⟨inferInstance, ‹GeometricallyConnected f›, fun s ↦ by
        have := hd s; rw [Nat.cast_one] at this; exact this⟩
  exact ⟨Y, T, F, g, g', isLocallyNoetherian_of_isOpenImmersion t, hFp, hFs,
    hFg, fun s ↦ by simpa using hFd s, by simpa using hi.map t.appTop.hom, hsq⟩

end AlgebraicGeometry

end
