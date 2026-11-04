module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale Galois covers of a limit come from a stage

Let `a` be a limit cone over a cofiltered system `F` of quasi-compact and quasi-separated
schemes with affine transition morphisms. Then every finite étale `G`-torsor over `a.pt`, for a
finite group `G`, is the base change of a finite étale `G`-torsor over some stage, equivariantly.
If the projections `a.pt ⟶ F i` are moreover flat, surjective and quasi-compact, the descended
torsor of a Galois cover is again a Galois cover. This is the descent of the Galois cover of the
generic fibre in the proof of [Stacks, Tag 0EZJ], and, without surjectivity, the spreading out of
a Galois cover of the generic fibre in the proof of [Stacks, Tag 0EYJ].

## Main results

* `AlgebraicGeometry.GaloisCoverLimits.exists_endo_descent`: an endomorphism of the base change
  to the limit of a scheme locally of finite presentation over a stage comes from an
  endomorphism over every sufficiently late stage.
* `AlgebraicGeometry.GaloisCoverLimits.exists_laterEndo_eq`: two such endomorphisms which agree
  over the limit agree over every sufficiently late stage.
* `AlgebraicGeometry.GaloisCoverLimits.exists_torsor_model`: the descent of a torsor.
* `AlgebraicGeometry.GaloisCoverLimits.exists_galoisCover_model`: the descent of a Galois cover,
  for flat, surjective and quasi-compact projections.

## Implementation notes

The cover itself descends by `AlgebraicGeometry.exists_finiteEtale_model`. Each element of `G`
then descends as an endomorphism, through Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` applied to the
system of base changes of the model, and the finitely many elements are brought to a common
stage. Everything is stated through the projection `Z ⟶ Vᵢ` of the cartesian square rather than
through isomorphisms of base changes: an endomorphism of `Vᵢ` descends an endomorphism of `Z`
when the projection intertwines them.

The group laws hold for the descended endomorphisms after composing with that projection, so by
Mathlib's `AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` they hold
after base change to a later stage (`AlgebraicGeometry.GaloisCoverLimits.laterEndo`). The
comparison map `G × Vᵢ ⟶ Vᵢ ×_{Fᵢ} Vᵢ` becomes the comparison map of `Z` after base change to the
limit (`AlgebraicGeometry.GaloisCoverLimits.isIso_galoisCoverComparison_iff_isIso_pullback_map`),
so it is an isomorphism after base change to a later stage by
`AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange` (Tag 081E). When the
projections are flat and surjective, connectedness of `Vᵢ` follows from surjectivity of the
projection `Z ⟶ Vᵢ`.

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace GaloisCoverLimits

variable {K : Type u} [Category.{u} K] (F : K ⥤ Scheme.{u}) (a : Cone F)

/-- The morphism from the vertex of a square over the limit to the base change of its right
edge to a later stage. -/
def stageLift {l d : K} (e : d ⟶ l) {W V : Scheme.{u}} (v : V ⟶ F.obj l) (P : W ⟶ V)
    (h : W ⟶ a.pt) (hP : P ≫ v = h ≫ a.π.app l) : W ⟶ pullback (F.map e) v :=
  pullback.lift (h ≫ a.π.app d) P (by rw [Category.assoc, a.w e, hP])

/-- The first projection of `stageLift` is the composite of `h` with the projection of the limit
to the later stage. -/
@[reassoc (attr := simp)]
theorem stageLift_fst {l d : K} (e : d ⟶ l) {W V : Scheme.{u}} (v : V ⟶ F.obj l) (P : W ⟶ V)
    (h : W ⟶ a.pt) (hP : P ≫ v = h ≫ a.π.app l) :
    stageLift F a e v P h hP ≫ pullback.fst (F.map e) v = h ≫ a.π.app d :=
  pullback.lift_fst _ _ _

/-- The second projection of `stageLift` is `P`. -/
@[reassoc (attr := simp)]
theorem stageLift_snd {l d : K} (e : d ⟶ l) {W V : Scheme.{u}} (v : V ⟶ F.obj l) (P : W ⟶ V)
    (h : W ⟶ a.pt) (hP : P ≫ v = h ≫ a.π.app l) :
    stageLift F a e v P h hP ≫ pullback.snd (F.map e) v = P :=
  pullback.lift_snd _ _ _

/-- A square over the base change `pullback.fst f v` is cartesian once its composite with
`pullback.snd f v` is cartesian over `v`. -/
private theorem isPullback_pullback_fst_of_comp_snd {X V Z A W : Scheme.{u}} {f : X ⟶ Z}
    {v : V ⟶ Z} {s : A ⟶ X} {r : W ⟶ A} {m : W ⟶ pullback f v}
    (hm : m ≫ pullback.fst f v = r ≫ s) (ho : IsPullback (m ≫ pullback.snd f v) r v (s ≫ f)) :
    IsPullback m r (pullback.fst f v) s :=
  ho.of_right hm (IsPullback.of_hasPullback _ _).flip

/-- A cartesian square over the limit restricts to a cartesian square over every later
stage. -/
theorem isPullback_stageLift {l d : K} (e : d ⟶ l) {W V : Scheme.{u}} (v : V ⟶ F.obj l)
    (P : W ⟶ V) (h : W ⟶ a.pt) (hP : IsPullback P h v (a.π.app l)) :
    IsPullback (stageLift F a e v P h hP.w) h (pullback.fst (F.map e) v) (a.π.app d) :=
  isPullback_pullback_fst_of_comp_snd (stageLift_fst F a e v P h hP.w)
    (by rwa [stageLift_snd, a.w e])

/-- If the projections of the system are flat and surjective, the projection from a cartesian
square over the limit to a stage is an epimorphism. -/
theorem epi_stageLift [∀ i, Flat (a.π.app i)] [∀ i, Surjective (a.π.app i)]
    {l d : K} (e : d ⟶ l) {W V : Scheme.{u}} (v : V ⟶ F.obj l) (P : W ⟶ V) (h : W ⟶ a.pt)
    (hP : IsPullback P h v (a.π.app l)) : Epi (stageLift F a e v P h hP.w) := by
  have hpb := isPullback_stageLift F a e v P h hP
  have h₁ : Flat (stageLift F a e v P h hP.w) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have h₂ : Surjective (stageLift F a e v P h hP.w) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  exact Flat.epi_of_flat_of_surjective _

/-- The projection from the base change of `V` to a later stage onto its base change to an
earlier one. -/
def stageTransfer {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j) (hk : k ≫ e = e₂)
    {V : Scheme.{u}} (v : V ⟶ F.obj l) : pullback (F.map e₂) v ⟶ pullback (F.map e) v :=
  pullback.lift (pullback.fst _ _ ≫ F.map k) (pullback.snd _ _) (by
    rw [Category.assoc, ← F.map_comp, hk, pullback.condition])

/-- The first projection of `stageTransfer` is the first projection followed by the transition
morphism `F.map k`. -/
@[reassoc (attr := simp)]
theorem stageTransfer_fst {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j) (hk : k ≫ e = e₂)
    {V : Scheme.{u}} (v : V ⟶ F.obj l) :
    stageTransfer F e e₂ k hk v ≫ pullback.fst (F.map e) v = pullback.fst (F.map e₂) v ≫ F.map k :=
  pullback.lift_fst _ _ _

/-- The second projection of `stageTransfer` is the second projection. -/
@[reassoc (attr := simp)]
theorem stageTransfer_snd {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j) (hk : k ≫ e = e₂)
    {V : Scheme.{u}} (v : V ⟶ F.obj l) :
    stageTransfer F e e₂ k hk v ≫ pullback.snd (F.map e) v = pullback.snd (F.map e₂) v :=
  pullback.lift_snd _ _ _

/-- Transferring in two steps is transferring along the composite. -/
theorem stageTransfer_comp {l j d₁ d₂ : K} (e : j ⟶ l) (e₁ : d₁ ⟶ l) (e₂ : d₂ ⟶ l)
    (k₀ : d₁ ⟶ j) (hk₀ : k₀ ≫ e = e₁) (k₁ : d₂ ⟶ d₁) (hk₁ : k₁ ≫ e₁ = e₂)
    (hk : (k₁ ≫ k₀) ≫ e = e₂) {V : Scheme.{u}} (v : V ⟶ F.obj l) :
    stageTransfer F e e₂ (k₁ ≫ k₀) hk v =
      stageTransfer F e₁ e₂ k₁ hk₁ v ≫ stageTransfer F e e₁ k₀ hk₀ v := by
  apply pullback.hom_ext
  · rw [stageTransfer_fst, Category.assoc, stageTransfer_fst, stageTransfer_fst_assoc, F.map_comp]
  · rw [stageTransfer_snd, Category.assoc, stageTransfer_snd, stageTransfer_snd]

/-- The base change to a later stage is the base change of the base change to an earlier one. -/
theorem isPullback_stageTransfer {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j)
    (hk : k ≫ e = e₂) {V : Scheme.{u}} (v : V ⟶ F.obj l) :
    IsPullback (stageTransfer F e e₂ k hk v) (pullback.fst (F.map e₂) v)
      (pullback.fst (F.map e) v) (F.map k) :=
  isPullback_pullback_fst_of_comp_snd (stageTransfer_fst F e e₂ k hk v) (by
    rw [stageTransfer_snd, ← F.map_comp, hk]
    exact (IsPullback.of_hasPullback _ _).flip)

/-- The base change to a later stage of an endomorphism of a base change of `V`. -/
def laterEndo {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j) (hk : k ≫ e = e₂)
    {V : Scheme.{u}} (v : V ⟶ F.obj l) (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    pullback (F.map e₂) v ⟶ pullback (F.map e₂) v :=
  pullback.lift (pullback.fst _ _) (stageTransfer F e e₂ k hk v ≫ χ ≫ pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc χ, hχ,
      stageTransfer_fst_assoc, ← F.map_comp, hk])

section LaterEndo

variable {l j d : K} (e : j ⟶ l) (e₂ : d ⟶ l) (k : d ⟶ j) (hk : k ≫ e = e₂)
  {V : Scheme.{u}} (v : V ⟶ F.obj l)

/-- The base change `laterEndo` of an endomorphism is a morphism over the later stage. -/
@[reassoc (attr := simp)]
theorem laterEndo_fst (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    laterEndo F e e₂ k hk v χ hχ ≫ pullback.fst (F.map e₂) v = pullback.fst (F.map e₂) v :=
  pullback.lift_fst _ _ _

/-- The second projection of `laterEndo` is the transfer followed by the endomorphism and the
second projection. -/
@[reassoc (attr := simp)]
theorem laterEndo_snd (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    laterEndo F e e₂ k hk v χ hχ ≫ pullback.snd (F.map e₂) v =
      stageTransfer F e e₂ k hk v ≫ χ ≫ pullback.snd (F.map e) v :=
  pullback.lift_snd _ _ _

/-- The transfer intertwines an endomorphism with its base change to a later stage. -/
@[reassoc]
theorem laterEndo_stageTransfer (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    laterEndo F e e₂ k hk v χ hχ ≫ stageTransfer F e e₂ k hk v =
      stageTransfer F e e₂ k hk v ≫ χ := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTransfer_fst, laterEndo_fst_assoc, Category.assoc, hχ,
      stageTransfer_fst]
  · rw [Category.assoc, stageTransfer_snd, laterEndo_snd, Category.assoc]

/-- The base change to a later stage of a composite of endomorphisms is the composite of their
base changes. -/
theorem laterEndo_comp (χ₁ χ₂ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (h₁ : χ₁ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v)
    (h₂ : χ₂ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v)
    (h₁₂ : (χ₁ ≫ χ₂) ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    laterEndo F e e₂ k hk v (χ₁ ≫ χ₂) h₁₂ =
      laterEndo F e e₂ k hk v χ₁ h₁ ≫ laterEndo F e e₂ k hk v χ₂ h₂ := by
  apply pullback.hom_ext
  · rw [laterEndo_fst, Category.assoc, laterEndo_fst, laterEndo_fst]
  · simp only [Category.assoc, laterEndo_snd, laterEndo_stageTransfer_assoc]

/-- The base change to a later stage of the identity is the identity. -/
theorem laterEndo_id (h : 𝟙 _ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) :
    laterEndo F e e₂ k hk v (𝟙 _) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [laterEndo_fst, Category.id_comp]
  · rw [laterEndo_snd, Category.id_comp, stageTransfer_snd, Category.id_comp]

/-- The projection from a square over the limit to a later stage, followed by the transfer, is
the projection to the earlier stage. -/
@[reassoc (attr := simp)]
theorem stageLift_stageTransfer {W : Scheme.{u}} (P : W ⟶ V) (h : W ⟶ a.pt)
    (hP : P ≫ v = h ≫ a.π.app l) :
    stageLift F a e₂ v P h hP ≫ stageTransfer F e e₂ k hk v = stageLift F a e v P h hP := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageTransfer_fst, stageLift_fst_assoc, stageLift_fst, a.w k]
  · rw [Category.assoc, stageTransfer_snd, stageLift_snd, stageLift_snd]

/-- An endomorphism intertwined with an endomorphism over the limit stays so after base change
to a later stage. -/
theorem stageLift_laterEndo {W : Scheme.{u}} (P : W ⟶ V) (h : W ⟶ a.pt)
    (hP : P ≫ v = h ≫ a.π.app l) (ψ : W ⟶ W) (hψ : ψ ≫ h = h)
    (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v)
    (hψχ : ψ ≫ stageLift F a e v P h hP = stageLift F a e v P h hP ≫ χ) :
    ψ ≫ stageLift F a e₂ v P h hP = stageLift F a e₂ v P h hP ≫ laterEndo F e e₂ k hk v χ hχ := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageLift_fst, Category.assoc, laterEndo_fst, stageLift_fst,
      ← Category.assoc, hψ]
  · rw [Category.assoc, stageLift_snd, Category.assoc, laterEndo_snd,
      stageLift_stageTransfer_assoc, ← Category.assoc, ← hψχ, Category.assoc, stageLift_snd]

end LaterEndo

/-- Passing an intertwined endomorphism from one stage to a later one. -/
theorem exists_endo_of_later {l j d : K} (e : j ⟶ l) (e' : d ⟶ j) {W V : Scheme.{u}}
    (v : V ⟶ F.obj l) (P : W ⟶ V) (h : W ⟶ a.pt) (hP : P ≫ v = h ≫ a.π.app l)
    (ψ : W ⟶ W) (hψ : ψ ≫ h = h)
    (χ : pullback (F.map e) v ⟶ pullback (F.map e) v)
    (hχ : χ ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v)
    (hψχ : ψ ≫ stageLift F a e v P h hP = stageLift F a e v P h hP ≫ χ) :
    ∃ χ' : pullback (F.map (e' ≫ e)) v ⟶ pullback (F.map (e' ≫ e)) v,
      χ' ≫ pullback.fst (F.map (e' ≫ e)) v = pullback.fst (F.map (e' ≫ e)) v ∧
      ψ ≫ stageLift F a (e' ≫ e) v P h hP = stageLift F a (e' ≫ e) v P h hP ≫ χ' :=
  ⟨laterEndo F e (e' ≫ e) e' rfl v χ hχ, laterEndo_fst F e (e' ≫ e) e' rfl v χ hχ,
    stageLift_laterEndo F a e (e' ≫ e) e' rfl v P h hP ψ hψ χ hχ hψχ⟩

/-- The projection from a cartesian square over the limit to a stage factors through the
isomorphism with the base change of the limit and the base change cone. -/
private theorem stageLift_eq_isoPullback_hom_comp (l : K) {W V : Scheme.{u}} (v : V ⟶ F.obj l)
    (P : W ⟶ V) (h : W ⟶ a.pt) (hP : IsPullback P h v (a.π.app l)) (j : Over l) :
    stageLift F a j.hom v P h hP.w =
      hP.flip.isoPullback.hom ≫ (Scheme.baseChangeCone F l (Over.mk v) a).π.app j := by
  let πj : pullback (a.π.app l) v ⟶ pullback (F.map j.hom) v :=
    (Scheme.baseChangeCone F l (Over.mk v) a).π.app j
  have hπ₁ : πj ≫ pullback.fst (F.map j.hom) v = pullback.fst (a.π.app l) v ≫ a.π.app j.left :=
    Scheme.baseChangeCone_π_fst F l (Over.mk v) a j
  have hπ₂ : πj ≫ pullback.snd (F.map j.hom) v = pullback.snd (a.π.app l) v :=
    Scheme.baseChangeCone_π_snd F l (Over.mk v) a j
  show stageLift F a j.hom v P h hP.w = hP.flip.isoPullback.hom ≫ πj
  apply pullback.hom_ext
  · rw [stageLift_fst, Category.assoc, hπ₁, ← Category.assoc, hP.flip.isoPullback_hom_fst]
  · rw [stageLift_snd, Category.assoc, hπ₂, hP.flip.isoPullback_hom_snd]

variable [IsCofiltered K] [∀ {i j : K} (g : i ⟶ j), IsAffineHom (F.map g)]
  [∀ i, CompactSpace (F.obj i)] [∀ i, QuasiSeparatedSpace (F.obj i)]

/-- **Endomorphisms over the limit descend.** Let `W ⟶ a.pt` be the base change of a
quasi-compact and quasi-separated scheme `V` locally of finite presentation over a stage `F l`.
An endomorphism `ψ` of `W` over `a.pt` comes from an endomorphism of the base change of `V` to
every stage below some stage `j`: the projection to that base change intertwines them. -/
@[ega "IV 8.8.3" "special case"]
theorem exists_endo_descent (ha : IsLimit a) (l : K) {W V : Scheme.{u}} (v : V ⟶ F.obj l)
    [LocallyOfFinitePresentation v] [QuasiCompact v] [QuasiSeparated v]
    (P : W ⟶ V) (h : W ⟶ a.pt) (hP : IsPullback P h v (a.π.app l))
    (ψ : W ⟶ W) (hψ : ψ ≫ h = h) :
    ∃ (j : K) (e : j ⟶ l), ∀ (d : K) (e'' : d ⟶ l) (e' : d ⟶ j), e' ≫ e = e'' →
      ∃ χ : pullback (F.map e'') v ⟶ pullback (F.map e'') v,
        χ ≫ pullback.fst (F.map e'') v = pullback.fst (F.map e'') v ∧
        ψ ≫ stageLift F a e'' v P h hP.w = stageLift F a e'' v P h hP.w ≫ χ := by
  let X : Over (F.obj l) := Over.mk v
  let G := Scheme.baseChangeDiagram F l X
  let c := Scheme.baseChangeCone F l X a
  have hc : IsLimit c := Scheme.isLimitBaseChangeCone F l X a ha
  have hGaff {j k : Over l} (g : j ⟶ k) : IsAffineHom (G.map g) :=
    Scheme.isAffineHom_baseChangeDiagram_map F l X g
  have hGc : ∀ j : Over l, CompactSpace (G.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (pullback (F.map j.hom) v : Scheme.{u}))
  have hGq : ∀ j : Over l, QuasiSeparatedSpace (G.obj j) := fun j ↦
    have : QuasiSeparatedSpace (pullback (F.map j.hom) v : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (F.map j.hom) v)
    inferInstanceAs (QuasiSeparatedSpace (pullback (F.map j.hom) v : Scheme.{u}))
  let ι : W ≅ pullback (a.π.app l) v := hP.flip.isoPullback
  have hι₂' : ι.inv ≫ P = pullback.snd (a.π.app l) v := hP.flip.isoPullback_inv_snd
  have hsv : pullback.snd (a.π.app l) v ≫ v = (ι.inv ≫ ψ ≫ P) ≫ v := by
    rw [Category.assoc, Category.assoc, hP.w, ← Category.assoc ψ, hψ, ← hP.w, ← Category.assoc,
      hι₂']
  have hcone : c.π ≫ Scheme.baseChangeStructureMap F l X =
      (Functor.const (Over l)).map ((ι.inv ≫ ψ ≫ P) ≫ v) := by
    ext j
    exact (Scheme.baseChangeCone_π_snd_assoc F l X a j v).trans hsv
  obtain ⟨j, b, hb₁, hb₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    (Scheme.baseChangeStructureMap F l X) v c hc (ι.inv ≫ ψ ≫ P) hcone
  let πj : pullback (a.π.app l) v ⟶ pullback (F.map j.hom) v := c.π.app j
  let b' : pullback (F.map j.hom) v ⟶ V := b
  have hb₁' : πj ≫ b' = ι.inv ≫ ψ ≫ P := hb₁
  have hb₂' : b' ≫ v = pullback.snd (F.map j.hom) v ≫ v := hb₂
  have hsl : stageLift F a j.hom v P h hP.w = ι.hom ≫ πj :=
    stageLift_eq_isoPullback_hom_comp F a l v P h hP j
  let χ : pullback (F.map j.hom) v ⟶ pullback (F.map j.hom) v :=
    pullback.lift (pullback.fst _ _) b' (by rw [pullback.condition, hb₂'])
  have hχ₁ : χ ≫ pullback.fst (F.map j.hom) v = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hχ₂ : χ ≫ pullback.snd (F.map j.hom) v = b' := pullback.lift_snd _ _ _
  have hψχ : ψ ≫ stageLift F a j.hom v P h hP.w = stageLift F a j.hom v P h hP.w ≫ χ := by
    apply pullback.hom_ext
    · rw [Category.assoc, stageLift_fst, Category.assoc, hχ₁, stageLift_fst, ← Category.assoc, hψ]
    · rw [Category.assoc, stageLift_snd, Category.assoc, hχ₂, hsl, Category.assoc, hb₁',
        Iso.hom_inv_id_assoc]
  refine ⟨j.left, j.hom, fun d e'' e' he ↦ ?_⟩
  subst he
  exact exists_endo_of_later F a j.hom e' v P h hP.w ψ hψ χ hχ₁ hψχ

/-- The group action on a finite étale cover determined by endomorphisms satisfying the group
laws. -/
def actionOfEndos {T : Scheme.{u}} (V : FiniteEtaleOver T) {G : Type v} [Group G]
    (χ : G → (V.left ⟶ V.left)) (hw : ∀ x, χ x ≫ V.hom = V.hom) (h1 : χ 1 = 𝟙 _)
    (hmul : ∀ x y, χ (x * y) = χ y ≫ χ x) : G →* Aut V :=
  (Aut.unitsEndEquivAut V).toMonoidHom.comp
    (MonoidHom.toHomUnits
      { toFun := fun x ↦ MorphismProperty.Over.homMk (χ x) (hw x) trivial
        map_one' := MorphismProperty.Over.Hom.ext h1
        map_mul' := fun x y ↦ MorphismProperty.Over.Hom.ext (hmul x y) })

/-- The automorphism `actionOfEndos V χ hw h1 hmul x` has underlying morphism `χ x`. -/
theorem actionOfEndos_hom_left {T : Scheme.{u}} (V : FiniteEtaleOver T) {G : Type v} [Group G]
    (χ : G → (V.left ⟶ V.left)) (hw : ∀ x, χ x ≫ V.hom = V.hom) (h1 : χ 1 = 𝟙 _)
    (hmul : ∀ x y, χ (x * y) = χ y ≫ χ x) (x : G) :
    (actionOfEndos V χ hw h1 hmul x).hom.left = χ x :=
  rfl

omit [∀ i, QuasiSeparatedSpace (F.obj i)] in
/-- **Equalities over the limit hold at a later stage.** Two endomorphisms of the base change of
`V` to a stage which agree after composing with the projection from the square over the limit
have equal base changes to every stage below some stage. -/
theorem exists_laterEndo_eq (ha : IsLimit a) (l : K) {W V : Scheme.{u}} (v : V ⟶ F.obj l)
    [LocallyOfFiniteType v] [QuasiCompact v]
    (P : W ⟶ V) (h : W ⟶ a.pt) (hP : IsPullback P h v (a.π.app l)) (jj : Over l)
    (χ₁ χ₂ : pullback (F.map jj.hom) v ⟶ pullback (F.map jj.hom) v)
    (h₁ : χ₁ ≫ pullback.fst (F.map jj.hom) v = pullback.fst (F.map jj.hom) v)
    (h₂ : χ₂ ≫ pullback.fst (F.map jj.hom) v = pullback.fst (F.map jj.hom) v)
    (heq : stageLift F a jj.hom v P h hP.w ≫ χ₁ = stageLift F a jj.hom v P h hP.w ≫ χ₂) :
    ∃ (j₀ : K) (k₀ : j₀ ⟶ jj.left), ∀ (d : K) (e₂ : d ⟶ l) (k : d ⟶ jj.left)
      (hk : k ≫ jj.hom = e₂) (k' : d ⟶ j₀), k' ≫ k₀ = k →
        laterEndo F jj.hom e₂ k hk v χ₁ h₁ = laterEndo F jj.hom e₂ k hk v χ₂ h₂ := by
  let X : Over (F.obj l) := Over.mk v
  let G := Scheme.baseChangeDiagram F l X
  let c := Scheme.baseChangeCone F l X a
  have hc : IsLimit c := Scheme.isLimitBaseChangeCone F l X a ha
  have hGaff {j k : Over l} (g : j ⟶ k) : IsAffineHom (G.map g) :=
    Scheme.isAffineHom_baseChangeDiagram_map F l X g
  have hGc : ∀ j : Over l, CompactSpace (G.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (pullback (F.map j.hom) v : Scheme.{u}))
  let ι : W ≅ pullback (a.π.app l) v := hP.flip.isoPullback
  let πj : pullback (a.π.app l) v ⟶ pullback (F.map jj.hom) v := c.π.app jj
  have hsl : stageLift F a jj.hom v P h hP.w = ι.hom ≫ πj :=
    stageLift_eq_isoPullback_hom_comp F a l v P h hP jj
  have h' : πj ≫ χ₁ = πj ≫ χ₂ := by
    rw [← Iso.cancel_iso_hom_left ι, ← Category.assoc, ← hsl, heq, hsl, Category.assoc]
  have hab : c.π.app jj ≫ χ₁ ≫ pullback.snd (F.map jj.hom) v =
      c.π.app jj ≫ χ₂ ≫ pullback.snd (F.map jj.hom) v :=
    (reassoc_of% h') (pullback.snd (F.map jj.hom) v)
  have hw (χ : pullback (F.map jj.hom) v ⟶ pullback (F.map jj.hom) v)
      (hχ : χ ≫ pullback.fst (F.map jj.hom) v = pullback.fst (F.map jj.hom) v) :
      (Scheme.baseChangeStructureMap F l X).app jj =
        (χ ≫ pullback.snd (F.map jj.hom) v) ≫ v := by
    show pullback.snd (F.map jj.hom) v ≫ v = (χ ≫ pullback.snd (F.map jj.hom) v) ≫ v
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hχ]
  obtain ⟨m, hm, hmeq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType G
    (Scheme.baseChangeStructureMap F l X) v c hc (χ₁ ≫ pullback.snd (F.map jj.hom) v)
    (χ₂ ≫ pullback.snd (F.map jj.hom) v) (hw χ₁ h₁) (hw χ₂ h₂) hab
  let Gm : pullback (F.map m.hom) v ⟶ pullback (F.map jj.hom) v := G.map hm
  have hGm : Gm = stageTransfer F jj.hom m.hom hm.left (Over.w hm) v := by
    apply pullback.hom_ext
    · rw [stageTransfer_fst]
      exact Scheme.baseChangeDiagram_map_fst F l X hm
    · rw [stageTransfer_snd]
      exact Scheme.baseChangeDiagram_map_snd F l X hm
  have hmeq' : Gm ≫ χ₁ ≫ pullback.snd (F.map jj.hom) v = Gm ≫ χ₂ ≫ pullback.snd (F.map jj.hom) v :=
    hmeq
  refine ⟨m.left, hm.left, fun d e₂ k hk k' hk' ↦ ?_⟩
  have hk'' : k' ≫ m.hom = e₂ := by
    rw [← Over.w hm, ← Category.assoc, hk', hk]
  have htr : stageTransfer F jj.hom e₂ k hk v =
      stageTransfer F m.hom e₂ k' hk'' v ≫
        stageTransfer F jj.hom m.hom hm.left (Over.w hm) v := by
    subst hk'
    exact stageTransfer_comp F jj.hom m.hom e₂ hm.left (Over.w hm) k' hk'' hk v
  apply pullback.hom_ext
  · rw [laterEndo_fst, laterEndo_fst]
  · rw [laterEndo_snd, laterEndo_snd, htr, ← hGm, Category.assoc, Category.assoc, hmeq']

/-- **Group actions over the limit descend.** An action of a finite group on the base change
`W ⟶ a.pt` of a quasi-compact and quasi-separated scheme `V` locally of finite presentation over
a stage, by endomorphisms over `a.pt`, comes from an action by endomorphisms of the base change of
`V` to a later stage, intertwined by the projection. -/
private theorem exists_endos_descent (ha : IsLimit a) (l : K) {W V : Scheme.{u}} (v : V ⟶ F.obj l)
    [LocallyOfFinitePresentation v] [QuasiCompact v] [QuasiSeparated v]
    (P : W ⟶ V) (h : W ⟶ a.pt) (hP : IsPullback P h v (a.π.app l))
    {G : Type v} [Group G] [Finite G] (ψ : G → (W ⟶ W)) (hψ : ∀ g, ψ g ≫ h = h)
    (h1 : ψ 1 = 𝟙 _) (hmul : ∀ x y, ψ (x * y) = ψ y ≫ ψ x) :
    ∃ (T : K) (e : T ⟶ l) (χ : G → (pullback (F.map e) v ⟶ pullback (F.map e) v)),
      (∀ g, χ g ≫ pullback.fst (F.map e) v = pullback.fst (F.map e) v) ∧ χ 1 = 𝟙 _ ∧
        (∀ x y, χ (x * y) = χ y ≫ χ x) ∧
        ∀ g, ψ g ≫ stageLift F a e v P h hP.w = stageLift F a e v P h hP.w ≫ χ g := by
  classical
  have hdesc (g : G) := exists_endo_descent F a ha l v P h hP (ψ g) (hψ g)
  choose j e hj using hdesc
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨d, hd⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image fun g : G ↦ Over.mk (e g))
  have hdg (g : G) : Nonempty (d ⟶ Over.mk (e g)) :=
    hd (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩)
  have hχ (g : G) := hj g d.left d.hom (hdg g).some.left (Over.w (hdg g).some)
  choose χ hχ₁ hχ₂ using hχ
  set L := stageLift F a d.hom v P h hP.w with hLdef
  have hone' : L ≫ χ 1 = L ≫ 𝟙 _ := by
    rw [← hχ₂ 1, h1, Category.id_comp, Category.comp_id]
  have hmul' (x y : G) : L ≫ χ (x * y) = L ≫ (χ y ≫ χ x) := by
    rw [← hχ₂, hmul, Category.assoc, hχ₂ x, ← Category.assoc, hχ₂ y, Category.assoc]
  have hcomp (x y : G) :
      (χ y ≫ χ x) ≫ pullback.fst (F.map d.hom) v = pullback.fst (F.map d.hom) v := by
    rw [Category.assoc, hχ₁, hχ₁]
  have hlaw (p : G × G) := exists_laterEndo_eq F a ha l v P h hP d
    (χ (p.1 * p.2)) (χ p.2 ≫ χ p.1) (hχ₁ _) (hcomp p.1 p.2) (hmul' p.1 p.2)
  choose jm km hm using hlaw
  obtain ⟨j₁, k₁, h₁⟩ := exists_laterEndo_eq F a ha l v P h hP d
    (χ 1) (𝟙 _) (hχ₁ 1) (Category.id_comp _) hone'
  obtain ⟨T, hT⟩ := IsCofiltered.inf_objs_exists
    (insert (Over.mk k₁) (Finset.univ.image fun p : G × G ↦ Over.mk (km p)))
  have hT₁ : Nonempty (T ⟶ Over.mk k₁) := hT (Finset.mem_insert_self _ _)
  have hTm (p : G × G) : Nonempty (T ⟶ Over.mk (km p)) :=
    hT (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))
  let κ : T.left ⟶ d.left := T.hom
  let eT : T.left ⟶ l := κ ≫ d.hom
  refine ⟨T.left, eT, fun g ↦ laterEndo F d.hom eT κ rfl v (χ g) (hχ₁ g),
    fun g ↦ laterEndo_fst F d.hom eT κ rfl v (χ g) (hχ₁ g), ?_, fun x y ↦ ?_,
    fun g ↦ stageLift_laterEndo F a d.hom eT κ rfl v P h hP.w (ψ g) (hψ g) (χ g) (hχ₁ g)
      (hχ₂ g)⟩
  · exact (h₁ T.left eT κ rfl hT₁.some.left (Over.w hT₁.some)).trans
      (laterEndo_id F d.hom eT κ rfl v _)
  · exact (hm (x, y) T.left eT κ rfl (hTm (x, y)).some.left (Over.w (hTm (x, y)).some)).trans
      (laterEndo_comp F d.hom eT κ rfl v (χ y) (χ x) (hχ₁ y) (hχ₁ x) _)

/-- If the comparison map of a finite étale cover of a stage with an action becomes an
isomorphism after base change to the limit, it is an isomorphism after base change to some later
stage. -/
private theorem exists_isIso_baseChange_galoisCoverComparisonOver (ha : IsLimit a) {G : Type v}
    [Group G] [Finite G] {i : K} (V : FiniteEtaleOver (F.obj i)) (act : Gᵐᵒᵖ →* Aut (Over.mk V.hom))
    [IsIso ((Over.pullback (a.π.app i)).map (galoisCoverComparisonOver V.hom act)).left] :
    ∃ (j : K) (g : j ⟶ i),
      IsIso ((Over.pullback (F.map g)).map (galoisCoverComparisonOver V.hom act)).left := by
  have hσA : finiteEtale (Limits.Sigma.desc fun _ : G ↦ V.hom) :=
    Stacks.FundamentalGroup.finiteEtale_sigmaDesc fun _ ↦ V.prop
  have : IsFinite (Limits.Sigma.desc fun _ : G ↦ V.hom) := hσA.1
  have : Etale (Limits.Sigma.desc fun _ : G ↦ V.hom) := hσA.2
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  have : CompactSpace ((Functor.fromPUnit (F.obj i)).obj V.right) :=
    inferInstanceAs (CompactSpace (F.obj i))
  have : QuasiSeparatedSpace ((Functor.fromPUnit (F.obj i)).obj V.right) :=
    inferInstanceAs (QuasiSeparatedSpace (F.obj i))
  have : CompactSpace (Over.mk (X := F.obj i) (Limits.Sigma.desc fun _ : G ↦ V.hom)).left :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.Sigma.desc fun _ : G ↦ V.hom)
  have : QuasiSeparatedSpace (Over.mk (X := F.obj i) (Limits.Sigma.desc fun _ : G ↦ V.hom)).left :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.Sigma.desc fun _ : G ↦ V.hom)
  have : CompactSpace (Over.mk (X := F.obj i) (pullback.fst V.hom V.hom ≫ V.hom)).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom V.hom ≫ V.hom)
  have : QuasiSeparatedSpace (Over.mk (X := F.obj i) (pullback.fst V.hom V.hom ≫ V.hom)).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom V.hom ≫ V.hom)
  have : Etale (galoisCoverComparisonOver V.hom act).left := by
    have : Etale ((galoisCoverComparisonOver V.hom act).left ≫
        pullback.fst V.hom V.hom ≫ V.hom) := by
      show Etale (Stacks.Descent.galoisCoverComparison V.hom act ≫
        pullback.fst V.hom V.hom ≫ V.hom)
      rw [galoisCoverComparison_fst_comp]
      infer_instance
    exact Etale.of_comp _ (pullback.fst V.hom V.hom ≫ V.hom)
  exact exists_isIso_baseChange_of_isIso_limitBaseChange F a ha i
    (Over.mk (X := F.obj i) (Limits.Sigma.desc fun _ : G ↦ V.hom))
    (Over.mk (X := F.obj i) (pullback.fst V.hom V.hom ≫ V.hom))
    (galoisCoverComparisonOver V.hom act)

/-- A torsor over the limit whose action descends to endomorphisms of the base change of a
finite étale cover `Y` of a stage, satisfying the group laws, comes from a torsor over a later
stage. -/
private theorem exists_torsor_model_of_endos (ha : IsLimit a) {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleOver a.pt) (aZ : Gᵐᵒᵖ →* Aut Z)
    [IsIso (Stacks.Descent.galoisCoverComparison Z.hom
      (((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut Z).comp aZ))]
    {l T : K} {Y : Scheme.{u}} (v : Y ⟶ F.obj l) [IsFinite v] [Etale v] (P : Z.left ⟶ Y)
    (hP : IsPullback P Z.hom v (a.π.app l)) (eT : T ⟶ l)
    (χT : Gᵐᵒᵖ → (pullback (F.map eT) v ⟶ pullback (F.map eT) v))
    (hχT₁ : ∀ g, χT g ≫ pullback.fst (F.map eT) v = pullback.fst (F.map eT) v)
    (hTone : χT 1 = 𝟙 _) (hTmul : ∀ x y, χT (x * y) = χT y ≫ χT x)
    (hactT : ∀ g, (aZ g).hom.left ≫ stageLift F a eT v P Z.hom hP.w =
      stageLift F a eT v P Z.hom hP.w ≫ χT g) :
    ∃ (i : K) (V : FiniteEtaleOver (F.obj i)) (act : Gᵐᵒᵖ →* Aut V) (P : Z.left ⟶ V.left),
      IsPullback P Z.hom V.hom (a.π.app i) ∧
        (∀ g, (aZ g).hom.left ≫ P = P ≫ (act g).hom.left) ∧
        IsIso (Stacks.Descent.galoisCoverComparison V.hom
          (((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut V).comp act)) := by
  let VT : FiniteEtaleOver (F.obj T) :=
    MorphismProperty.Over.mk ⊤ (pullback.fst (F.map eT) v) ⟨inferInstance, inferInstance⟩
  let aT : Gᵐᵒᵖ →* Aut (Over.mk VT.hom) :=
    ((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut VT).comp
      (actionOfEndos VT χT hχT₁ hTone hTmul)
  have : IsIso ((Over.pullback (a.π.app T)).map (galoisCoverComparisonOver VT.hom aT)).left :=
    (isIso_galoisCoverComparison_iff_isIso_pullback_map (isPullback_stageLift F a eT v P Z.hom hP)
      aT (((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut Z).comp aZ) hactT).mp
      inferInstance
  obtain ⟨T₂, g₂, hiso⟩ := exists_isIso_baseChange_galoisCoverComparisonOver F a ha VT aT
  let e₂ : T₂ ⟶ l := g₂ ≫ eT
  let χ₂ (g : Gᵐᵒᵖ) := laterEndo F eT e₂ g₂ rfl v (χT g) (hχT₁ g)
  have hχ₂₁ (g : Gᵐᵒᵖ) : χ₂ g ≫ pullback.fst (F.map e₂) v = pullback.fst (F.map e₂) v :=
    laterEndo_fst F eT e₂ g₂ rfl v (χT g) (hχT₁ g)
  have h2one : χ₂ 1 = 𝟙 _ := by
    show laterEndo F eT e₂ g₂ rfl v (χT 1) (hχT₁ 1) = 𝟙 _
    simp only [hTone]
    exact laterEndo_id F eT e₂ g₂ rfl v _
  have h2mul (x y : Gᵐᵒᵖ) : χ₂ (x * y) = χ₂ y ≫ χ₂ x := by
    show laterEndo F eT e₂ g₂ rfl v (χT (x * y)) (hχT₁ _) = _
    simp only [hTmul]
    exact laterEndo_comp F eT e₂ g₂ rfl v (χT y) (χT x) (hχT₁ y) (hχT₁ x) _
  let V₂ : FiniteEtaleOver (F.obj T₂) :=
    MorphismProperty.Over.mk ⊤ (pullback.fst (F.map e₂) v) ⟨inferInstance, inferInstance⟩
  let act₂ := actionOfEndos V₂ χ₂ hχ₂₁ h2one h2mul
  let a₂ : Gᵐᵒᵖ →* Aut (Over.mk V₂.hom) :=
    ((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut V₂).comp act₂
  have htr (g : Gᵐᵒᵖ) : (a₂ g).hom.left ≫ stageTransfer F eT e₂ g₂ rfl v =
      stageTransfer F eT e₂ g₂ rfl v ≫ (aT g).hom.left :=
    laterEndo_stageTransfer F eT e₂ g₂ rfl v (χT g) (hχT₁ g)
  exact ⟨T₂, V₂, act₂, stageLift F a e₂ v P Z.hom hP.w, isPullback_stageLift F a e₂ v P Z.hom hP,
    fun g ↦ stageLift_laterEndo F a eT e₂ g₂ rfl v P Z.hom hP.w (aZ g).hom.left
      (MorphismProperty.Over.w (aZ g).hom) (χT g) (hχT₁ g) (hactT g),
    (isIso_galoisCoverComparison_iff_isIso_pullback_map
      (isPullback_stageTransfer F eT e₂ g₂ rfl v) aT a₂ htr).mpr hiso⟩

/-- **Finite étale torsors over a limit come from a stage.** Over the limit of a cofiltered
system of quasi-compact and quasi-separated schemes with affine transition morphisms, a finite
étale cover with an action of a finite group `G` making it a `G`-torsor is the base change of a
finite étale cover of a stage with an action making it a `G`-torsor, by a cartesian square whose
top map is equivariant. No flatness or surjectivity of the projections is needed. -/
theorem exists_torsor_model (ha : IsLimit a) {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleOver a.pt) (aZ : Gᵐᵒᵖ →* Aut Z)
    [IsIso (Stacks.Descent.galoisCoverComparison Z.hom
      (((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut Z).comp aZ))] :
    ∃ (i : K) (V : FiniteEtaleOver (F.obj i)) (act : Gᵐᵒᵖ →* Aut V) (P : Z.left ⟶ V.left),
      IsPullback P Z.hom V.hom (a.π.app i) ∧
        (∀ g, (aZ g).hom.left ≫ P = P ≫ (act g).hom.left) ∧
        IsIso (Stacks.Descent.galoisCoverComparison V.hom
          (((MorphismProperty.Over.forget finiteEtale ⊤ _).mapAut V).comp act)) := by
  obtain ⟨l, B, ⟨eB⟩⟩ := exists_finiteEtale_model F a ha Z
  have hB₁ : IsFinite B.hom := B.prop.1
  have hB₂ : Etale B.hom := B.prop.2
  let φ : Z.left ⟶ pullback B.hom (a.π.app l) := eB.hom.left
  let φ' : pullback B.hom (a.π.app l) ⟶ Z.left := eB.inv.left
  let eL : Z.left ≅ pullback B.hom (a.π.app l) :=
    { hom := φ
      inv := φ'
      hom_inv_id := congrArg (fun m ↦ m.left) eB.hom_inv_id
      inv_hom_id := congrArg (fun m ↦ m.left) eB.inv_hom_id }
  have heL : eL.hom ≫ pullback.snd B.hom (a.π.app l) = Z.hom := MorphismProperty.Over.w eB.hom
  set P₀ : Z.left ⟶ B.left := eL.hom ≫ pullback.fst B.hom (a.π.app l) with hP₀def
  have hP₀w : P₀ ≫ B.hom = Z.hom ≫ a.π.app l := by
    rw [hP₀def, Category.assoc, pullback.condition, ← Category.assoc, heL]
  have hP₀ : IsPullback P₀ Z.hom B.hom (a.π.app l) :=
    IsPullback.of_iso_pullback ⟨hP₀w⟩ eL rfl heL
  have hZ1 : (aZ 1).hom.left = 𝟙 _ := by
    rw [map_one]
    rfl
  have hZmul (x y : Gᵐᵒᵖ) : (aZ (x * y)).hom.left = (aZ y).hom.left ≫ (aZ x).hom.left := by
    rw [map_mul]
    rfl
  have : Finite Gᵐᵒᵖ := Finite.of_equiv G MulOpposite.opEquiv
  obtain ⟨T, eT, χT, hχT₁, hTone, hTmul, hactT⟩ := exists_endos_descent F a ha l B.hom P₀ Z.hom
    hP₀ (fun g ↦ (aZ g).hom.left) (fun g ↦ MorphismProperty.Over.w (aZ g).hom) hZ1 hZmul
  exact exists_torsor_model_of_endos F a ha Z aZ B.hom P₀ hP₀ eT χT hχT₁ hTone hTmul hactT

/-- **Finite étale Galois covers of a limit come from a stage.** Over the limit of a cofiltered
system of quasi-compact and quasi-separated schemes with affine transition morphisms and flat,
surjective, quasi-compact projections, a finite étale Galois cover is the base change of a finite
étale Galois cover of a stage, by a cartesian square whose top map is equivariant. -/
theorem exists_galoisCover_model (ha : IsLimit a)
    [∀ i, Flat (a.π.app i)] [∀ i, Surjective (a.π.app i)] [∀ i, QuasiCompact (a.π.app i)]
    {G : Type v} [Group G] [Finite G] (Z : FiniteEtaleGaloisCover a.pt G) :
    ∃ (i : K) (V : FiniteEtaleGaloisCover (F.obj i) G) (P : Z.obj.left ⟶ V.obj.left),
      IsPullback P Z.obj.hom V.obj.hom (a.π.app i) ∧
        ∀ g, (Z.action g).hom.left ≫ P = P ≫ (V.action g).hom.left := by
  obtain ⟨i, V, act, P, hP, hact, hiso⟩ := exists_torsor_model F a ha Z.obj Z.action
  have hPs : Surjective P := MorphismProperty.of_isPullback hP.flip inferInstance
  have hconn : ConnectedSpace V.left :=
    Function.Surjective.connectedSpace hPs.surj P.continuous
  exact ⟨i, ⟨V, hconn, act, hiso⟩, P, hP, hact⟩

end GaloisCoverLimits

end AlgebraicGeometry

end
