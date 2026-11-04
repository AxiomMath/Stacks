module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImage

/-!
# Base change along a limit of cartesian diagrams of schemes

Let `I` be a preordered set and let `(X_i)`, `(S_i)`, `(T_i)`, `(Y_i)` be inverse systems of
schemes over `I` fitting into an inverse system of squares

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

Writing `X = lim X_i`, `S = lim S_i`, `T = lim T_i`, `Y = lim Y_i` with projections
`r_i : X ⟶ X_i`, `s_i : S ⟶ S_i`, `p_i : T ⟶ T_i`, `q_i : Y ⟶ Y_i`, the four limit morphisms
`f`, `g`, `h`, `e` form a square on the limits, and Stacks 0EZT asserts that this square is again
cartesian and that base change for the higher direct images passes from the levels to the limit.

## Main definitions

* `Stacks.EtaleCohomology.LimitBaseChange.sourceTerm`,
  `Stacks.EtaleCohomology.LimitBaseChange.targetTerm` — the terms `s_i^{-1}R^q g_{i,*}ℱ_i` and
  `r_i^{-1}R^q h_{i,*}e_i^{-1}ℱ_i` of the two colimit diagrams of Stacks 0EYM.
* `Stacks.EtaleCohomology.LimitBaseChange.projectionPushforwardComparison`,
  `Stacks.EtaleCohomology.LimitBaseChange.projectionPullbackComparison` — the comparisons
  `f_* s_{i,*} ≅ r_{i,*} f_{i,*}` and `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}` attached to the
  projection square `f ≫ s_i = r_i ≫ f_i`.
* `Stacks.EtaleCohomology.LimitBaseChange.stageComparison` — the base change map of the `i`-th
  square, pulled back to `X`, as a map `f^{-1}s_i^{-1}R^q g_{i,*}ℱ_i ⟶ r_i^{-1}R^q
  h_{i,*}e_i^{-1}ℱ_i`.
* `Stacks.EtaleCohomology.LimitBaseChange.pullbackTerm`,
  `Stacks.EtaleCohomology.LimitBaseChange.pullbackTermIso` — the term `q_i^{-1}e_i^{-1}ℱ_i` of
  the colimit presentation of `e^{-1}ℱ` and its identification with the inverse image of the
  `i`-th term of a colimit presentation of `ℱ`.
* `Stacks.EtaleCohomology.LimitBaseChange.isColimitMapCoconePullback` — the inverse image of a
  colimit presentation of `ℱ` is a colimit presentation of `e^{-1}ℱ`.

## Main results

* `Stacks.EtaleCohomology.LimitBaseChange.limitSquare_comm` — the square on the limits commutes.
* `Stacks.EtaleCohomology.LimitBaseChange.isPullback_limitSquare` — **the square on the limits is
  cartesian**, the assertion of the setup of Stacks 0EZT. Only the four limit properties and the
  levelwise cartesian squares are used.
* `Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit` — **conclusion (2)
  of Stacks 0EZT**: if base change for `R^q` holds on every level, it holds on the limit.

## Implementation notes

The four limit morphisms are carried as named morphisms together with the equations
`f ≫ s_i = r_i ≫ f_i` characterising them, rather than written as
`Stacks.EtaleCohomology.LimitHigherDirectImage.limitMorphism`; that morphism together with
`Stacks.EtaleCohomology.LimitHigherDirectImage.limitMorphism_comp_π` exhibits them, and carrying
the equations keeps the statements free of transport along the universal property.

The source assumes `I` directed, the transition morphisms affine and the `g_i` quasi-compact and
quasi-separated. None of those enters the cartesianness of the limit square, so none of them is a
hypothesis of `isPullback_limitSquare`; they are what the colimit assertion of Stacks 0EYM needs.

The colimit assertion of Stacks 0EYM, `R^q g_* ℱ = colim_i s_i^{-1}R^q g_{i,*}ℱ_i`, enters
`isIso_higherBaseChangeMapAb_limit` as hypotheses: the two instances that the source's proof
cites — one for `g` with the system `ℱ_i`, one for `h` with the system `e_i^{-1}ℱ_i` — are given
as colimit presentations, that is a diagram over `I`, isomorphisms identifying its terms with
`sourceTerm` resp. `targetTerm`, and a colimit cocone whose vertex is the higher direct image at
the limit. The comparison `α` of the two diagrams and its compatibility with the legs, which is
the pasting of base change maps of Stacks 0E47, is given as well. From those inputs the proof is
the source's argument: inverse image is a left adjoint, so it carries the first presentation to a
colimit presentation of `f^{-1}R^q g_* ℱ`, and a map of colimit cocones which is invertible on
every term is invertible.

Conclusion (1) of Stacks 0EZT, the same statement for a system of sheaves of sets and the
underived direct images, is not treated here.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.LimitBaseChange

variable {I : Type v} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (cX : Cone DX) (cS : Cone DS) (cT : Cone DT) (cY : Cone DY)
  (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)

/-! ### The square on the limits -/

/-- Pasting a square with a projection square: the legs `y ≫ a = b ≫ h` and `x ≫ p = a ≫ f`
give `y ≫ x ≫ p = b ≫ h ≫ f`. -/
private theorem comp_comp_eq_of_comm {C : Type*} [Category* C] {A B P Q R S : C}
    {y : A ⟶ B} {a : B ⟶ P} {b : A ⟶ Q} {h : Q ⟶ P} {x : B ⟶ R} {p : R ⟶ S} {f : P ⟶ S}
    (hy : y ≫ a = b ≫ h) (hx : x ≫ p = a ≫ f) : y ≫ x ≫ p = b ≫ h ≫ f := by
  rw [hx, ← Category.assoc, hy, Category.assoc]

/-- A morphism `n` into the limit composes with `hL` to `u` iff it does so level by level. -/
private theorem comp_eq_iff_forall {D₁ D₂ : Iᵒᵖ ⥤ Scheme.{u}} (h : D₁ ⟶ D₂) {c₁ : Cone D₁}
    {c₂ : Cone D₂} (hc₂ : IsLimit c₂) (hL : c₁.pt ⟶ c₂.pt)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ c₂.π.app i = c₁.π.app i ≫ h.app i) {A : Scheme.{u}}
    (n : A ⟶ c₁.pt) (u : A ⟶ c₂.pt) :
    n ≫ hL = u ↔ ∀ i : Iᵒᵖ, (n ≫ c₁.π.app i) ≫ h.app i = u ≫ c₂.π.app i := by
  refine ⟨fun H i => ?_, fun H => hc₂.hom_ext fun i => ?_⟩
  · rw [← H, Category.assoc, Category.assoc, hhL i]
  · rw [Category.assoc, hhL i, ← Category.assoc, H i]

/-- **The square on the limits commutes.** It is the unique square through which the limit of the
levelwise squares factors, so its commutativity is read off the levels against the projections of
the limit of the `S_i`. -/
theorem limitSquare_comm (hcS : IsLimit cS)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) :
    hL ≫ fL = eL ≫ gL := by
  refine hcS.hom_ext fun i => ?_
  rw [Category.assoc, comp_comp_eq_of_comm (hhL i) (hfL i), Category.assoc,
    comp_comp_eq_of_comm (heL i) (hgL i), w i]

/-- **The square on the limits is cartesian**, the assertion of the setup of Stacks 0EZT. A
morphism to `X` and a morphism to `T` agreeing over `S` induce, level by level, a morphism to
`Y_i` through the cartesian square at `i`; these are compatible with the transitions because the
two legs of the square at a larger index determine a morphism, so they define a morphism to
`Y = lim Y_i`, and the same two uniqueness statements make it the unique one. -/
@[stacks 0EZT "the square on the limits of an inverse system of cartesian squares is cartesian"]
theorem isPullback_limitSquare (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT)
    (hcY : IsLimit cY)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i)) :
    IsPullback hL eL fL gL := by
  have wL : hL ≫ fL = eL ≫ gL :=
    limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL fun i => (hsq i).w
  have key : ∀ (A : Scheme.{u}) (u : A ⟶ cX.pt) (v : A ⟶ cT.pt), u ≫ fL = v ≫ gL →
      ∃! m : A ⟶ cY.pt, m ≫ hL = u ∧ m ≫ eL = v := by
    intro A u v huv
    have hcomm : ∀ i : Iᵒᵖ,
        (u ≫ cX.π.app i) ≫ f.app i = (v ≫ cT.π.app i) ≫ g.app i := by
      intro i
      rw [Category.assoc, ← hfL i, Category.assoc, ← hgL i, ← Category.assoc, ← Category.assoc,
        huv]
    let m : ∀ i : Iᵒᵖ, A ⟶ DY.obj i := fun i =>
      (hsq i).lift (u ≫ cX.π.app i) (v ≫ cT.π.app i) (hcomm i)
    have hmh : ∀ i : Iᵒᵖ, m i ≫ h.app i = u ≫ cX.π.app i := fun i => (hsq i).lift_fst _ _ _
    have hme : ∀ i : Iᵒᵖ, m i ≫ e.app i = v ≫ cT.π.app i := fun i => (hsq i).lift_snd _ _ _
    let mcone : Cone DY :=
      { pt := A
        π :=
          { app := m
            naturality := by
              intro i j a
              refine (Category.id_comp _).trans ((hsq j).hom_ext ?_ ?_).symm
              · rw [Category.assoc, ← LimitHigherDirectImage.transition_comm h a,
                  ← Category.assoc, hmh i, Category.assoc, cX.w a, hmh j]
              · rw [Category.assoc, ← LimitHigherDirectImage.transition_comm e a,
                  ← Category.assoc, hme i, Category.assoc, cT.w a, hme j] } }
    have hfac : ∀ i : Iᵒᵖ, hcY.lift mcone ≫ cY.π.app i = m i := fun i => hcY.fac mcone i
    refine ⟨hcY.lift mcone,
      ⟨(comp_eq_iff_forall h hcX hL hhL _ _).2 fun i => by rw [hfac i, hmh i],
        (comp_eq_iff_forall e hcT eL heL _ _).2 fun i => by rw [hfac i, hme i]⟩, ?_⟩
    intro n hn
    refine hcY.hom_ext fun i => ?_
    rw [hfac i]
    exact (hsq i).hom_ext ((comp_eq_iff_forall h hcX hL hhL _ _).1 hn.1 i |>.trans (hmh i).symm)
      ((comp_eq_iff_forall e hcT eL heL _ _).1 hn.2 i |>.trans (hme i).symm)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk wL
    (fun s => (key s.pt s.fst s.snd s.condition).choose)
    (fun s => (key s.pt s.fst s.snd s.condition).choose_spec.1.1)
    (fun s => (key s.pt s.fst s.snd s.condition).choose_spec.1.2)
    fun s n hn₁ hn₂ => (key s.pt s.fst s.snd s.condition).choose_spec.2 n ⟨hn₁, hn₂⟩)

/-! ### Transfer of invertibility along a colimit -/

/-- A map of colimit cocones which is invertible on every term of the diagrams is invertible. -/
public theorem isIso_of_isColimit {C : Type*} [Category* C] {J : Type*} [Category* J]
    {K L : J ⥤ C} {c : Cocone K} (hc : IsColimit c) {d : Cocone L} (hd : IsColimit d)
    (α : K ⟶ L) (hα : ∀ j, IsIso (α.app j)) (β : c.pt ⟶ d.pt)
    (hβ : ∀ j, c.ι.app j ≫ β = α.app j ≫ d.ι.app j) : IsIso β := by
  have : ∀ j, IsIso (α.app j) := hα
  have hiso : IsIso α := NatIso.isIso_of_isIso_app α
  have hβ' : β = (hc.coconePointsIsoOfNatIso hd (asIso α)).hom := by
    refine hc.hom_ext fun j => ?_
    rw [hβ j, IsColimit.comp_coconePointsIsoOfNatIso_hom]
    rfl
  rw [hβ']
  infer_instance

/-! ### The two colimit diagrams and the levelwise base change map -/

variable (F : EtaleSheafSystem DT Ab.{u + 1}) (q : ℕ)

/-- The term `s_i^{-1}R^q g_{i,*}ℱ_i` on `S` of the colimit diagram of Stacks 0EYM for `g`. -/
abbrev sourceTerm (i : Iᵒᵖ) : Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb (cS.π.app i)).obj
    (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))

/-- The term `r_i^{-1}R^q h_{i,*}e_i^{-1}ℱ_i` on `X` of the colimit diagram of Stacks 0EYM for
`h` and the system of inverse images `e_i^{-1}ℱ_i`. -/
abbrev targetTerm (i : Iᵒᵖ) : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb (cX.π.app i)).obj
    (((smallEtalePushforwardAb (h.app i)).rightDerived q).obj
      ((smallEtalePullbackAb (e.app i)).obj (F.obj i)))

/-- The comparison `f_* s_{i,*} ≅ r_{i,*} f_{i,*}` of the two composite direct images of the
projection square `f ≫ s_i = r_i ≫ f_i`, assembled from the composition isomorphism for direct
image of abelian étale sheaves. -/
def projectionPushforwardComparison
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ) :
    smallEtalePushforwardAb fL ⋙ smallEtalePushforwardAb (cS.π.app i) ≅
      smallEtalePushforwardAb (cX.π.app i) ⋙ smallEtalePushforwardAb (f.app i) :=
  smallEtalePushforwardAbCompIso fL (cS.π.app i) ≪≫
    eqToIso (congrArg smallEtalePushforwardAb (hfL i)) ≪≫
      (smallEtalePushforwardAbCompIso (cX.π.app i) (f.app i)).symm

/-- The comparison `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}` of the two composite inverse images of the
projection square `f ≫ s_i = r_i ≫ f_i`: the conjugate of
`Stacks.EtaleCohomology.LimitBaseChange.projectionPushforwardComparison` under the
inverse-image/direct-image adjunctions. -/
def projectionPullbackComparison
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ) :
    smallEtalePullbackAb (cS.π.app i) ⋙ smallEtalePullbackAb fL ≅
      smallEtalePullbackAb (f.app i) ⋙ smallEtalePullbackAb (cX.π.app i) :=
  Adjunction.leftAdjointUniq
    ((smallEtaleAdjunctionAb (cS.π.app i)).comp (smallEtaleAdjunctionAb fL))
    (Adjunction.ofNatIsoRight
      ((smallEtaleAdjunctionAb (f.app i)).comp (smallEtaleAdjunctionAb (cX.π.app i)))
      (projectionPushforwardComparison f cX cS fL hfL i).symm)

/-- **The levelwise comparison of the two colimit diagrams of Stacks 0EYM**: the base change map
of the `i`-th square of the system on higher direct images, pulled back to `X` along the
projection `r_i` and read on the source through the comparison
`Stacks.EtaleCohomology.LimitBaseChange.projectionPullbackComparison`. -/
def stageComparison (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).obj (sourceTerm g cS F q i) ⟶ targetTerm h e cX F q i :=
  (projectionPullbackComparison f cX cS fL hfL i).hom.app
      (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i)) ≫
    (smallEtalePullbackAb (cX.π.app i)).map
      ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i))

/-- The levelwise comparison is invertible as soon as the base change map of the `i`-th square
is: the other two factors are isomorphisms. -/
theorem isIso_stageComparison
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ)
    (hi : IsIso ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app
      (F.obj i))) :
    IsIso (stageComparison f g h e cX cS fL F q w hfL i) := by
  have := hi
  exact inferInstanceAs (IsIso (_ ≫ _))

/-! ### The inverse image of a colimit presentation -/

/-- The term `q_i^{-1}e_i^{-1}ℱ_i` on `Y` of the colimit presentation of `e^{-1}ℱ`, the system of
sheaves to which Stacks 0EYM is applied for `h`. -/
abbrev pullbackTerm (i : Iᵒᵖ) : Sheaf (smallEtaleTopology cY.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb (cY.π.app i)).obj ((smallEtalePullbackAb (e.app i)).obj (F.obj i))

/-- **The inverse image of a colimit presentation is a colimit presentation**, the first step of
the proof of Stacks 0EZT: inverse image is a left adjoint, so a cocone presenting
`ℱ = colim_i p_i^{-1}ℱ_i` on `T` is carried to a cocone presenting `e^{-1}ℱ` on `Y`. -/
def isColimitMapCoconePullback
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (K : I ⥤ Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (κ : K ⟶ (Functor.const I).obj 𝓕) (hκ : IsColimit (Cocone.mk 𝓕 κ)) :
    IsColimit ((smallEtalePullbackAb eL).mapCocone (Cocone.mk 𝓕 κ)) := by
  have := (smallEtaleAdjunctionAb eL).leftAdjoint_preservesColimits
  exact isColimitOfPreserves (smallEtalePullbackAb eL) hκ

/-- The terms of the inverse image of a colimit presentation of `ℱ = colim_i p_i^{-1}ℱ_i` are the
`q_i^{-1}e_i^{-1}ℱ_i`, which is the second step of the source's identification
`e^{-1}ℱ = colim_i e^{-1}p_i^{-1}ℱ_i = colim_i q_i^{-1}e_i^{-1}ℱ_i`: the comparison of the two
composite inverse images of the projection square `e ≫ p_i = q_i ≫ e_i`. -/
def pullbackTermIso
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (K : I ⥤ Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (ρ : ∀ i : I, K.obj i ≅
      (smallEtalePullbackAb (cT.π.app (Opposite.op i))).obj (F.obj (Opposite.op i)))
    (i : I) :
    (K ⋙ smallEtalePullbackAb eL).obj i ≅ pullbackTerm e cY F (Opposite.op i) :=
  (smallEtalePullbackAb eL).mapIso (ρ i) ≪≫
    (projectionPullbackComparison e cY cT eL heL (Opposite.op i)).app (F.obj (Opposite.op i))

/-! ### Conclusion (2) of Stacks 0EZT -/

/-- **Conclusion (2) of Stacks 0EZT.** Let `(ℱ_i, φ_{i'i})` be a system of abelian sheaves on
`(T_i)` and let `ℱ` on `T` be a sheaf whose higher direct images along the limit are presented,
as in Stacks 0EYM, as the colimits of the `s_i^{-1}R^q g_{i,*}ℱ_i` and of the
`r_i^{-1}R^q h_{i,*}e_i^{-1}ℱ_i`, compatibly with the levelwise base change maps. If the base
change map of every level is an isomorphism, so is the base change map of the limit square. -/
@[stacks 0EZT "conclusion (2): base change for the higher direct images passes to the limit"]
theorem isIso_higherBaseChangeMapAb_limit
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (wL : hL ≫ fL = eL ≫ gL)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (Kg : I ⥤ Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1})
    (ρg : ∀ i : I, Kg.obj i ≅ sourceTerm g cS F q (Opposite.op i))
    (κg : Kg ⟶ (Functor.const I).obj
      (((smallEtalePushforwardAb gL).rightDerived q).obj 𝓕))
    (hκg : IsColimit (Cocone.mk _ κg))
    (Kh : I ⥤ Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ρh : ∀ i : I, Kh.obj i ≅ targetTerm h e cX F q (Opposite.op i))
    (κh : Kh ⟶ (Functor.const I).obj
      (((smallEtalePushforwardAb hL).rightDerived q).obj ((smallEtalePullbackAb eL).obj 𝓕)))
    (hκh : IsColimit (Cocone.mk _ κh))
    (α : Kg ⋙ smallEtalePullbackAb fL ⟶ Kh)
    (hα : ∀ i : I, (smallEtalePullbackAb fL).map (ρg i).hom ≫
      stageComparison f g h e cX cS fL F q w hfL (Opposite.op i) = α.app i ≫ (ρh i).hom)
    (hκ : ∀ i : I, (smallEtalePullbackAb fL).map (κg.app i) ≫
      (higherBaseChangeMapAb fL gL hL eL wL q).app 𝓕 = α.app i ≫ κh.app i)
    (hstage : ∀ i : Iᵒᵖ,
      IsIso ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app
        (F.obj i))) :
    IsIso ((higherBaseChangeMapAb fL gL hL eL wL q).app 𝓕) := by
  have := (smallEtaleAdjunctionAb fL).leftAdjoint_preservesColimits
  refine isIso_of_isColimit
    (isColimitOfPreserves (smallEtalePullbackAb fL) hκg) hκh α (fun i => ?_) _ fun i => hκ i
  have h₁ : IsIso (stageComparison f g h e cX cS fL F q w hfL (Opposite.op i)) :=
    isIso_stageComparison f g h e cX cS fL F q w hfL (Opposite.op i) (hstage (Opposite.op i))
  have h₂ : IsIso (α.app i ≫ (ρh i).hom) := by rw [← hα i]; infer_instance
  exact IsIso.of_isIso_comp_right (α.app i) (ρh i).hom

end Stacks.EtaleCohomology.LimitBaseChange

end
