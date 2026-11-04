module

public import Mathlib.CategoryTheory.Limits.Comma
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Approximation
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Retract
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Descending an object of finite presentation along a cofiltered limit

Let a scheme be the limit of a cofiltered system of quasi-compact and quasi-separated schemes
whose transition morphisms are affine. A scheme of finite presentation over the limit is the base
change of a scheme of finite presentation over one of the stages. This is part (1) of tag 01ZM.

## Main definitions

* `AlgebraicGeometry.LimitFPObjectDescent.pullbackArrowDiagram`: the inverse system of base
  changes, over the right-hand limit, of an inverse system of arrows of schemes.

## Main results

* `AlgebraicGeometry.LimitFPObjectDescent.finitePresentation_of_finiteType_over_terminal`: a
  morphism between schemes of finite type over the terminal scheme is of finite presentation.
* `AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation`: tag 01ZM part (1).

## Implementation notes

The route is the Stacks proof. Approximate the structure morphism of the given scheme by an
inverse system of morphisms between schemes of finite type over the terminal scheme `Spec ℤ`,
which is tag 0GS1; such morphisms are automatically of *finite presentation*, the terminal scheme
being locally Noetherian. Base changing that system along the projections of its own target cone
produces an inverse system over the limit whose own limit is the given scheme, and finite
presentation of the given scheme factors the identity of its underlying scheme through one stage
of that system. The given scheme is therefore a *retract*, over the limit, of the base change of
a scheme of finite presentation over a stage of the approximating system of targets; one further
factorization moves that stage to a stage of the originally given system, and
`AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_retract` -- the second half of this
part, already proved -- descends the retract.

The index category of the given system is only essentially small relative to the scheme universe,
so the factorizations use the universe-independent forms
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`
and `AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall` rather than Mathlib's, whose index
universes are tied to the scheme universe. `CategoryTheory.InitiallySmall` is discharged from
essential smallness, which also supplies `CategoryTheory.LocallySmall`.

The limiting cone of the approximating system is transported along the identification of its
vertex with the given arrow before anything else is done with it, so that the cone's vertex is
literally that arrow and the base-changed diagram is a diagram over the given base. The two
projections of a cone in an arrow category are limiting because the two functors to the source
and target jointly reflect limits in a comma category and preserve the cone constructed from the
two separate limits; the base-changed diagram's cone is then limiting by a direct check, its lifts
being the lifts of the source cone.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0GS1](https://stacks.math.columbia.edu/tag/0GS1)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.LimitFPObjectDescent

/-! ### Finite presentation over the terminal scheme -/

/-- A morphism between schemes of finite type over the terminal scheme is of finite presentation.
The terminal scheme is `Spec ℤ`, which is Noetherian, so both schemes are locally Noetherian and
the structure morphism of the source is of finite presentation; tag 02FV then factors it. -/
@[sga "3 VIB 10.8" "special case"]
theorem finitePresentation_of_finiteType_over_terminal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType (terminal.from X)] [QuasiCompact (terminal.from X)]
    [LocallyOfFiniteType (terminal.from Y)] [QuasiCompact (terminal.from Y)] :
    FinitePresentation f := by
  obtain ⟨_, _⟩ := finiteTypeStage_compact_qs X
  obtain ⟨_, _⟩ := finiteTypeStage_compact_qs Y
  have : LocallyOfFinitePresentation (terminal.from X) :=
    finiteTypeStage_locallyFinitePresentation X
  have hX : FinitePresentation (f ≫ terminal.from Y) := by
    rw [terminal.comp_from]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact finitePresentation_of_comp f (terminal.from Y) hX

/-- The source of a quasi-compact quasi-separated morphism to a compact quasi-separated space is
compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : QuasiCompact f ∧ QuasiSeparated f) [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  obtain ⟨_, _⟩ := h
  exact ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

/-! ### The two projections of a limiting cone of arrows -/

/-- The source and target cones of a limiting cone in the arrow category are limiting. -/
def arrowConeProjectionsIsLimit {J : Type u} [Category.{u} J] (A : J ⥤ Arrow Scheme.{u})
    (c : Cone A) (hc : IsLimit c) [HasLimit (A ⋙ Arrow.leftFunc)]
    [HasLimit (A ⋙ Arrow.rightFunc)] :
    IsLimit (Arrow.leftFunc.mapCone c) × IsLimit (Arrow.rightFunc.mapCone c) := by
  have hd := Comma.coneOfPreservesIsLimit A
    (limit.isLimit (A ⋙ Arrow.leftFunc)) (limit.isLimit (A ⋙ Arrow.rightFunc))
  have : PreservesLimit A Arrow.leftFunc :=
    preservesLimit_of_preserves_limit_cone hd (limit.isLimit (A ⋙ Arrow.leftFunc))
  have : PreservesLimit A Arrow.rightFunc :=
    preservesLimit_of_preserves_limit_cone hd (limit.isLimit (A ⋙ Arrow.rightFunc))
  exact ⟨isLimitOfPreserves _ hc, isLimitOfPreserves _ hc⟩

/-! ### Base changing a system of arrows along its own target cone -/

section Diagram

variable {J : Type u} [Category.{u} J] (A : J ⥤ Arrow Scheme.{u}) (c : Cone A)

/-- The transition morphism of the base-changed system: the base change of the transition
morphism `A.map e` of the system of arrows along the target components of the two cone legs. -/
noncomputable def arrowBaseChangeMap {j k : J} (e : j ⟶ k) :
    pullback (A.obj j).hom (c.π.app j).right ⟶ pullback (A.obj k).hom (c.π.app k).right :=
  pullback.lift (pullback.fst (A.obj j).hom (c.π.app j).right ≫ (A.map e).left)
    (pullback.snd (A.obj j).hom (c.π.app j).right) (by
      rw [Category.assoc, Arrow.w, ← Category.assoc, pullback.condition, Category.assoc,
        ← Arrow.comp_right, c.w])

/-- The first projection of `arrowBaseChangeMap A c e` is the first projection followed by
`(A.map e).left`. -/
@[simp, reassoc (attr := simp)]
lemma arrowBaseChangeMap_fst {j k : J} (e : j ⟶ k) :
    arrowBaseChangeMap A c e ≫ pullback.fst (A.obj k).hom (c.π.app k).right =
      pullback.fst (A.obj j).hom (c.π.app j).right ≫ (A.map e).left :=
  pullback.lift_fst _ _ _

/-- The morphism `arrowBaseChangeMap A c e` commutes with the second projections. -/
@[simp, reassoc (attr := simp)]
lemma arrowBaseChangeMap_snd {j k : J} (e : j ⟶ k) :
    arrowBaseChangeMap A c e ≫ pullback.snd (A.obj k).hom (c.π.app k).right =
      pullback.snd (A.obj j).hom (c.π.app j).right :=
  pullback.lift_snd _ _ _

/-- The leg at `j` of the cone over the base-changed system, out of the source of the cone's own
vertex. -/
noncomputable def arrowBaseChangeLeg (j : J) :
    c.pt.left ⟶ pullback (A.obj j).hom (c.π.app j).right :=
  pullback.lift (c.π.app j).left c.pt.hom (c.π.app j).w

/-- The first projection of `arrowBaseChangeLeg A c j` is the source component of the cone leg
at `j`. -/
@[simp, reassoc (attr := simp)]
lemma arrowBaseChangeLeg_fst (j : J) :
    arrowBaseChangeLeg A c j ≫ pullback.fst (A.obj j).hom (c.π.app j).right =
      (c.π.app j).left :=
  pullback.lift_fst _ _ _

/-- The second projection of `arrowBaseChangeLeg A c j` is the structure morphism of the cone
vertex `c.pt`. -/
@[simp, reassoc (attr := simp)]
lemma arrowBaseChangeLeg_snd (j : J) :
    arrowBaseChangeLeg A c j ≫ pullback.snd (A.obj j).hom (c.π.app j).right = c.pt.hom :=
  pullback.lift_snd _ _ _

/-- The inverse system over `c.pt.right` whose value at `j` is the base change of `A.obj j` along
the target component of the cone leg at `j`.

It is `reducible`, as `AlgebraicGeometry.baseChangeDiagram` is, so that the source of a morphism
out of one of its objects is the pullback itself for `rw` and for instance search rather than only
for elaboration. -/
noncomputable abbrev pullbackArrowDiagram : J ⥤ Over c.pt.right where
  obj j := Over.mk (pullback.snd (A.obj j).hom (c.π.app j).right)
  map {_ _} e := Over.homMk (arrowBaseChangeMap A c e) (arrowBaseChangeMap_snd A c e)
  map_id j := by ext; apply pullback.hom_ext <;> simp
  map_comp e f := by ext; apply pullback.hom_ext <;> simp [Category.assoc]

/-- The cone over the base-changed system whose vertex is the cone's own vertex, viewed as an
object over its target. -/
noncomputable abbrev pullbackArrowCone : Cone (pullbackArrowDiagram A c) where
  pt := Over.mk c.pt.hom
  π.app j := Over.homMk (arrowBaseChangeLeg A c j) (arrowBaseChangeLeg_snd A c j)
  π.naturality j k e := by
    have h : (c.π.app j).left ≫ (A.map e).left = (c.π.app k).left := by
      rw [← Arrow.comp_left, c.w]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [h]

/-- The transition morphisms of the base-changed system are affine when those of the sources and
the target components of the cone legs are. -/
lemma isAffineHom_pullbackArrowDiagram_map [∀ j, IsAffineHom (c.π.app j).right] {j k : J}
    (e : j ⟶ k) [IsAffineHom (A.map e).left] :
    IsAffineHom ((pullbackArrowDiagram A c ⋙ Over.forget c.pt.right).map e) := by
  have (l : J) : IsAffineHom (pullback.fst (A.obj l).hom (c.π.app l).right) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (A.obj l).hom (c.π.app l).right).flip inferInstance
  have : IsAffineHom ((pullbackArrowDiagram A c ⋙ Over.forget c.pt.right).map e ≫
      pullback.fst (A.obj k).hom (c.π.app k).right) := by
    simpa [pullbackArrowDiagram] using inferInstanceAs
      (IsAffineHom (pullback.fst (A.obj j).hom (c.π.app j).right ≫ (A.map e).left))
  exact IsAffineHom.of_comp _ (pullback.fst (A.obj k).hom (c.π.app k).right)

/-! ### Clean-typed steps of the universal property

Every step of the universal property below is stated for *variables* ranging over the pullbacks
themselves rather than over the objects of
`AlgebraicGeometry.LimitFPObjectDescent.pullbackArrowDiagram`. The source of a morphism out of
such an object is the pullback only after unfolding `CategoryTheory.Over.mk`, which elaboration
performs and `rw` does not, so inside these lemmas every rewrite matches and the connection to
the diagram is made once, by `exact`. -/

section Steps

variable {W : Scheme.{u}}

/-- Naturality of the first projection, which is what makes the induced cone on the sources a
cone. -/
lemma arrowBaseChange_fst_naturality {j k : J} (e : j ⟶ k)
    (p : W ⟶ pullback (A.obj j).hom (c.π.app j).right)
    (q : W ⟶ pullback (A.obj k).hom (c.π.app k).right)
    (h : p ≫ arrowBaseChangeMap A c e = q) :
    q ≫ pullback.fst (A.obj k).hom (c.π.app k).right =
      (p ≫ pullback.fst (A.obj j).hom (c.π.app j).right) ≫ (A.map e).left := by
  rw [← h, Category.assoc, arrowBaseChangeMap_fst, Category.assoc]

/-- A morphism into the source of the cone's vertex whose composites with the first projections
are those of `p` is compatible with the structure morphisms. -/
lemma arrowBaseChange_structure {j : J} (p : W ⟶ pullback (A.obj j).hom (c.π.app j).right)
    (L : W ⟶ c.pt.left) (m : W ⟶ c.pt.right)
    (hL : L ≫ (c.π.app j).left = p ≫ pullback.fst (A.obj j).hom (c.π.app j).right)
    (hm : p ≫ pullback.snd (A.obj j).hom (c.π.app j).right = m) :
    (L ≫ c.pt.hom) ≫ (c.π.app j).right = m ≫ (c.π.app j).right := by
  have hcw : (c.π.app j).left ≫ (A.obj j).hom = c.pt.hom ≫ (c.π.app j).right := (c.π.app j).w
  rw [Category.assoc, ← hcw, ← Category.assoc, hL, Category.assoc,
    pullback.condition, ← Category.assoc, hm]

/-- The factorization: a morphism into the source of the cone's vertex compatible with both
projections factors `p` through the cone's leg. -/
lemma arrowBaseChangeLeg_fac {j : J} (p : W ⟶ pullback (A.obj j).hom (c.π.app j).right)
    (L : W ⟶ c.pt.left) (m : W ⟶ c.pt.right)
    (hL : L ≫ (c.π.app j).left = p ≫ pullback.fst (A.obj j).hom (c.π.app j).right)
    (hm : p ≫ pullback.snd (A.obj j).hom (c.π.app j).right = m) (hLm : L ≫ c.pt.hom = m) :
    L ≫ arrowBaseChangeLeg A c j = p := by
  apply pullback.hom_ext
  · rw [Category.assoc, arrowBaseChangeLeg_fst, hL]
  · rw [Category.assoc, arrowBaseChangeLeg_snd, hLm, ← hm]

/-- The uniqueness step: two factorizations of `p` through the cone's leg agree after composing
with the first projection, which is what the limit on the sources detects. -/
lemma arrowBaseChangeLeg_uniq {j : J} (p : W ⟶ pullback (A.obj j).hom (c.π.app j).right)
    (L L' : W ⟶ c.pt.left)
    (hL : L ≫ (c.π.app j).left = p ≫ pullback.fst (A.obj j).hom (c.π.app j).right)
    (hL' : L' ≫ arrowBaseChangeLeg A c j = p) :
    L' ≫ (c.π.app j).left = L ≫ (c.π.app j).left := by
  rw [hL, ← arrowBaseChangeLeg_fst A c j, ← Category.assoc, hL']

end Steps

end Diagram

/-- The cone over the base-changed system is limiting whenever the two projections of the given
cone of arrows are. A lift is the lift of the induced cone on the sources; its two pullback
components are that lift and the structure morphism of the test object. -/
def pullbackArrowConeIsLimit {J : Type u} [Category.{u} J] (A : J ⥤ Arrow Scheme.{u})
    (c : Cone A) (hl : IsLimit (Arrow.leftFunc.mapCone c))
    (hr : IsLimit (Arrow.rightFunc.mapCone c)) : IsLimit (pullbackArrowCone A c) := by
  -- The two limit hypotheses are restated with the arrow projections written out; each
  -- restatement holds by definitional unfolding, which `exact` performs and `rw` does not.
  have extL : ∀ {W : Scheme.{u}} (m₁ m₂ : W ⟶ c.pt.left),
      (∀ j, m₁ ≫ (c.π.app j).left = m₂ ≫ (c.π.app j).left) → m₁ = m₂ :=
    fun _ _ h => hl.hom_ext h
  have extR : ∀ {W : Scheme.{u}} (m₁ m₂ : W ⟶ c.pt.right),
      (∀ j, m₁ ≫ (c.π.app j).right = m₂ ≫ (c.π.app j).right) → m₁ = m₂ :=
    fun _ _ h => hr.hom_ext h
  -- The cone on the sources induced by a test cone.
  let sourceCone (s : Cone (pullbackArrowDiagram A c)) : Cone (A ⋙ Arrow.leftFunc) := {
    pt := s.pt.left
    π := {
      app j := (s.π.app j).left ≫ pullback.fst (A.obj j).hom (c.π.app j).right
      naturality := fun j k e => (Category.id_comp _).trans
        (arrowBaseChange_fst_naturality A c e (s.π.app j).left (s.π.app k).left
          (congrArg Over.Hom.left (s.w e))) } }
  have facL : ∀ (s : Cone (pullbackArrowDiagram A c)) (j : J),
      hl.lift (sourceCone s) ≫ (c.π.app j).left =
        (s.π.app j).left ≫ pullback.fst (A.obj j).hom (c.π.app j).right :=
    fun s j => hl.fac (sourceCone s) j
  have hw : ∀ s : Cone (pullbackArrowDiagram A c),
      hl.lift (sourceCone s) ≫ c.pt.hom = s.pt.hom := fun s =>
    extR _ _ fun j => arrowBaseChange_structure A c (s.π.app j).left (hl.lift (sourceCone s))
      s.pt.hom (facL s j) (Over.w (s.π.app j))
  exact
    { lift s := Over.homMk (hl.lift (sourceCone s)) (hw s)
      fac s j := Over.OverMorphism.ext <| arrowBaseChangeLeg_fac A c (s.π.app j).left
        (hl.lift (sourceCone s)) s.pt.hom (facL s j) (Over.w (s.π.app j)) (hw s)
      uniq s m hm := Over.OverMorphism.ext <| extL _ _ fun j => arrowBaseChangeLeg_uniq A c
        (s.π.app j).left (hl.lift (sourceCone s)) m.left (facL s j)
        (congrArg Over.Hom.left (hm j)) }

/-- The source of the vertex of a cone of arrows with limiting projections is, over the target,
a retract of a stage of the base-changed system, when the arrows of the system are of finite
presentation, the vertex is of finite presentation with quasi-compact quasi-separated target, and
the transition morphisms of the sources and the target legs are affine. -/
theorem exists_retract_pullbackArrowDiagram {J : Type u} [Category.{u} J] [IsCofiltered J]
    [EssentiallySmall.{u} J] (A : J ⥤ Arrow Scheme.{u}) (c : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone c)) (hr : IsLimit (Arrow.rightFunc.mapCone c))
    (hA : ∀ j, FinitePresentation (A.obj j).hom) [LocallyOfFinitePresentation c.pt.hom]
    [CompactSpace c.pt.right] [QuasiSeparatedSpace c.pt.right]
    [∀ j, IsAffineHom (c.π.app j).right] [∀ {j k : J} (e : j ⟶ k), IsAffineHom (A.map e).left] :
    ∃ (j : J) (s : Over.mk c.pt.hom ⟶ (pullbackArrowDiagram A c).obj j)
      (r : (pullbackArrowDiagram A c).obj j ⟶ Over.mk c.pt.hom), s ≫ r = 𝟙 _ := by
  let E := pullbackArrowDiagram A c
  let B := E ⋙ Over.forget c.pt.right
  have hE (j : J) : FinitePresentation (E.obj j).hom :=
    finitePresentation_overPullback (c.π.app j).right (Over.mk (A.obj j).hom) (hA j)
  have hB (j : J) := compactSpace_and_quasiSeparatedSpace_of_hom (E.obj j).hom (hE j).2
  have (j : J) : CompactSpace (B.obj j) := (hB j).1
  have (j : J) : QuasiSeparatedSpace (B.obj j) := (hB j).2
  have {j k : J} (e : j ⟶ k) : IsAffineHom (B.map e) := isAffineHom_pullbackArrowDiagram_map A c e
  have : InitiallySmall.{u} J := initiallySmall_of_essentiallySmall J
  let t : B ⟶ (Functor.const _).obj c.pt.right := {
    app j := (E.obj j).hom
    naturality := fun _ _ e => (Over.w (E.map e)).trans (Category.comp_id _).symm }
  obtain ⟨j, g, hg, hg'⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall B
      ((Over.forget c.pt.right).mapCone (pullbackArrowCone A c)) t c.pt.hom
      (isLimitOfPreserves _ (pullbackArrowConeIsLimit A c hl hr)) (𝟙 c.pt.left)
      (by
        ext k
        exact (arrowBaseChangeLeg_snd A c k).trans (Category.id_comp c.pt.hom).symm)
  exact ⟨j, (pullbackArrowCone A c).π.app j, Over.homMk g hg', Over.OverMorphism.ext hg⟩

/-- A scheme over the limit that is a retract of the base change, along a morphism from the limit,
of a morphism between schemes of finite type over the terminal scheme is the base change of a
scheme of finite presentation over some stage. -/
theorem exists_model_of_retract_of_finiteType {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (X : Over c.pt) {Z T : Scheme.{u}} (h : Z ⟶ T)
    [LocallyOfFiniteType (terminal.from Z)] [QuasiCompact (terminal.from Z)]
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] (a : c.pt ⟶ T)
    (s : X ⟶ (Over.pullback a).obj (Over.mk h)) (r : (Over.pullback a).obj (Over.mk h) ⟶ X)
    (hsr : s ≫ r = 𝟙 X) :
    ∃ (i : I) (Xᵢ : Over (D.obj i)),
      FinitePresentation Xᵢ.hom ∧ Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ) := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have : LocallyOfFinitePresentation (terminal.from T) :=
    finiteTypeStage_locallyFinitePresentation _
  obtain ⟨i, f, hf, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall D c
      (NatTrans.mk (fun k => terminal.from (D.obj k))) (terminal.from T) hc a (by ext; simp)
  let η := overPullbackCompIso f (c.π.app i) a hf (Over.mk h)
  exact exists_model_of_retract D c hc X i _
    (finitePresentation_overPullback f _ (finitePresentation_of_finiteType_over_terminal h))
    (s ≫ η.inv) (η.hom ≫ r) (by simpa using hsr)

/-! ### Part (1) of tag 01ZM -/

/-- **Stacks Project, Tag 01ZM, part (1).** A scheme of finite presentation over the limit of a
cofiltered system of quasi-compact and quasi-separated schemes with affine transition morphisms is
obtained by base change from some stage. -/
@[stacks 01ZM "part (1)",
  sga "3 VIB 10.0" "(ii)",
  sga "4 VII 5.2" "(b)",
  sga "4 VII 5.3" "essential surjectivity"]
theorem exists_model_of_finitePresentation {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (X : Over c.pt) (hX : FinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (D.obj i)),
      FinitePresentation Xᵢ.hom ∧ Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ) := by
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have (i : I) : IsAffineHom (c.π.app i) := isAffineHom_π_app_of_initiallySmall D c hc i
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨hc₁, hc₂⟩ : CompactSpace c.pt ∧ QuasiSeparatedSpace c.pt :=
    compactSpace_and_quasiSeparatedSpace_of_hom (c.π.app i₀) ⟨inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation X.hom := hX.1
  obtain ⟨hX₁, hX₂⟩ := compactSpace_and_quasiSeparatedSpace_of_hom X.hom hX.2
  -- Tag 0GS1: approximate `X.hom` by morphisms between schemes of finite type over `Spec ℤ`.
  obtain ⟨J, hJ, hJn, hJd, A, d, hlft, hrft, haff, ⟨hd⟩, ⟨ε⟩⟩ :=
    exists_isLimit_finiteType_arrow X.hom
  -- Transport the cone so that its vertex is literally the arrow `X.hom`.
  let d' := d.extend ε.inv
  have hd' : IsLimit d' := hd.ofIsoLimit (Cone.ext ε fun j => by simp [d'])
  have : CompactSpace d'.pt.right := inferInstanceAs (CompactSpace c.pt)
  have : QuasiSeparatedSpace d'.pt.right := inferInstanceAs (QuasiSeparatedSpace c.pt)
  have (j : Jᵒᵖ) : LocallyOfFiniteType (terminal.from (A.obj j).left) := (hlft j).1
  have (j : Jᵒᵖ) : QuasiCompact (terminal.from (A.obj j).left) := (hlft j).2
  have (j : Jᵒᵖ) : LocallyOfFiniteType (terminal.from (A.obj j).right) := (hrft j).1
  have (j : Jᵒᵖ) : QuasiCompact (terminal.from (A.obj j).right) := (hrft j).2
  have {j k : Jᵒᵖ} (e : j ⟶ k) : IsAffineHom ((A ⋙ Arrow.leftFunc).map e) := (haff e).1
  have {j k : Jᵒᵖ} (e : j ⟶ k) : IsAffineHom ((A ⋙ Arrow.rightFunc).map e) := (haff e).2
  -- Tag 01YX: both projected systems have limits, so both projections of `d'` are limiting.
  have : HasLimit (A ⋙ Arrow.leftFunc) := hasLimit_of_isCofiltered_of_isAffineHom _
  have : HasLimit (A ⋙ Arrow.rightFunc) := hasLimit_of_isCofiltered_of_isAffineHom _
  obtain ⟨hl, hr⟩ := arrowConeProjectionsIsLimit A d' hd'
  have (j : Jᵒᵖ) : IsAffineHom (d'.π.app j).right :=
    isAffineHom_π_app (A ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone d') hr j
  have : LocallyOfFinitePresentation d'.pt.hom := hX.1
  have {j k : Jᵒᵖ} (e : j ⟶ k) : IsAffineHom (A.map e).left := (haff e).1
  -- Base change the system of arrows along the projections of its own target cone; finite
  -- presentation of `X` factors the identity through a stage: `X` is a retract.
  obtain ⟨j, s, r, hsr⟩ := exists_retract_pullbackArrowDiagram A d' hl hr fun j =>
    finitePresentation_of_finiteType_over_terminal (A.obj j).hom
  -- Move the target stage of the approximating system to a stage of the given system.
  exact exists_model_of_retract_of_finiteType D c hc X (A.obj j).hom (d'.π.app j).right s r hsr

end AlgebraicGeometry.LimitFPObjectDescent

end

end
