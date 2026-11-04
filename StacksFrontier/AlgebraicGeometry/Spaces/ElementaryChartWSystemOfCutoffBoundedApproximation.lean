module

public import StacksFrontier.AlgebraicGeometry.Spaces.CutoffBoundedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedStageChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# The W-systems of Stacks 07SU over approximations bounded by the cutoff

In the proof of absolute Noetherian approximation, Stacks 07SU, one is given an elementary chart
`f : V ⟶ X` (an étale morphism from a quasi-compact separated scheme which is an isomorphism over
the complement of an open subspace `U ⊆ X`), with `W = f⁻¹(U)`, and a Noetherian approximation
`U = lim U_i`. The source then says: "by Stacks 07SK there is an étale morphism `W_0 ⟶ U_0` of
finite presentation whose base change to `U` is `W`; set `W_i = W_0 ×_{U_0} U_i`; by Stacks 07SL
we may assume `W_i ⟶ U_i` étale, and by Stacks 07SR that the `W_i` are schemes". This file carries
that out for an approximation indexed below the cutoff, with the forms of Stacks 07SK, 07SL and
07SR for systems bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`):

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation` (07SK)
  descends `W ⟶ U` to `Y₀ ⟶ U_{i₀}`;
* `AlgebraicGeometry.Space.exists_isEtale_pullbackMap_of_isCutoffBoundedSystem` (07SL) makes
  `Y₀ ×_{U_{i₀}} U_i ⟶ U_i` étale for `i ≥ i₁`;
* `Space.DescentSituation.exists_isRepresentable_system_obj_of_isCutoffBoundedSystem` (07SR)
  makes some `Y₀ ×_{U_{i₀}} U_i` a scheme, and then every later one is, being affine over it.

Restricting the approximation to the tail of the index set past these stages gives the W-system
(`AlgebraicGeometry.Space.ElementaryChart.WSystem`) over an approximation with no more stages than
the given one. So `AlgebraicGeometry.Space.ElementaryChart.HasCutoffBoundedWSystems` holds, and
with it Stacks 07SU over `Spec ℤ` with a system bounded by the cutoff, and the assembly of Stacks
0A0X under that bound with its inputs about Stacks 07SU and 07SK discharged.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianApproximation.tail`: the restriction of a Noetherian
  approximation to the tail of its index set above an index.
* `AlgebraicGeometry.Space.tailBaseChange`: the base changes `D_j ×_{D_{i₀}} Y₀` over the tail
  above `i₀` of an inverse system.

## Main results

* `AlgebraicGeometry.Space.ElementaryChart.nonempty_wSystem_of_isRepresentable`: a W-system from
  a system of presheaves over the stages, with the defining cartesian squares, étale over the
  stages, quasi-compact and representable.
* `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`: the W-systems exist over
  approximations indexed below the cutoff.
* `AlgebraicGeometry.Space.hasCutoffBoundedNoetherianApproximation_of_isQuasiCompactSpace`:
  Stacks 07SU over `Spec ℤ`, indexed below the cutoff.
* `Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_isCutoffBoundedSystem`
  and `AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem`: the assembly
  of Stacks 0A0X under the cutoff bound, from Stacks 0A0W and 08K1 alone.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Tails of Noetherian approximations -/

namespace NoetherianApproximation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The restriction of a Noetherian approximation to a tail.** The stages `X_j` with
`i₁ ≤ j` of a Noetherian approximation `X = lim X_i` form a Noetherian approximation of the same
presheaf: the tail is directed and its inclusion is final, so `X` is also the limit of the
restricted system. -/
abbrev tail (A : NoetherianApproximation B S hS hZ X) (i₁ : A.I) :
    NoetherianApproximation B S hS hZ X :=
  letI := A.preorder
  letI := A.isDirected
  haveI := final_tailInclusion i₁
  { I := {j : A.I // i₁ ≤ j}
    nonempty := ⟨⟨i₁, le_rfl⟩⟩
    isDirected := isDirected_tail i₁
    diagram := (tailInclusion i₁).op ⋙ A.diagram
    isAlgebraicSpace := fun _ => A.isAlgebraicSpace _
    isAffineHom_map := fun _ => A.isAffineHom_map _
    isAbsolutelyQuasiSeparated := fun _ => A.isAbsolutelyQuasiSeparated _
    isFiniteTypeOverIntegers := fun _ => A.isFiniteTypeOverIntegers _
    π := Functor.whiskerLeft (tailInclusion i₁).op A.π
    isLimit := (Functor.Initial.isLimitWhiskerEquiv (tailInclusion i₁).op _).symm A.isLimit }

/-- A tail of a Noetherian approximation has no more stages than the approximation. -/
theorem mk_tail_le (A : NoetherianApproximation B S hS hZ X) (i₁ : A.I) :
    #(A.tail i₁).I ≤ #A.I :=
  let := A.preorder
  Cardinal.mk_subtype_le _

end NoetherianApproximation

/-! ### Base changes over a tail -/

section TailBaseChange

variable {C : Type*} [Category C] [HasPullbacks C] {I : Type u} [Preorder I]
  (D : Iᵒᵖ ⥤ C) (i₀ : I) {Y₀ : C} (y : Y₀ ⟶ D.obj (op i₀))

omit [HasPullbacks C] in
/-- Two morphisms between the same stages of an inverse system indexed by the opposite of a
preorder have the same image. -/
theorem map_eq_map_of_preorder {a b : Iᵒᵖ} (x x' : a ⟶ b) : D.map x = D.map x' :=
  congrArg D.map (Subsingleton.elim x x')

/-- **The base changes over a tail.** For an inverse system `D` indexed by the opposite of a
preorder, an index `i₀` and `y : Y₀ ⟶ D i₀`, the system `j ↦ D_j ×_{D_{i₀}} Y₀` over the tail
`j ≥ i₀`, with the transition morphisms induced by those of `D`. -/
abbrev tailBaseChange : {j : I // i₀ ≤ j}ᵒᵖ ⥤ C where
  obj j := pullback (D.map (homOfLE j.unop.2).op) y
  map {a b} g := pullback.lift
    (pullback.fst _ _ ≫ D.map (homOfLE (show b.unop.1 ≤ a.unop.1 from leOfHom g.unop)).op)
    (pullback.snd _ _) (by
      rw [Category.assoc, ← D.map_comp, ← pullback.condition]
      exact congrArg (pullback.fst _ _ ≫ ·) (map_eq_map_of_preorder D _ _))
  map_id a := pullback.hom_ext (by
      rw [pullback.lift_fst, Category.id_comp]
      refine (congrArg (pullback.fst _ _ ≫ ·) (map_eq_map_of_preorder D _ (𝟙 _))).trans ?_
      rw [D.map_id, Category.comp_id]) (by rw [pullback.lift_snd, Category.id_comp])
  map_comp f g := pullback.hom_ext (by
      rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.assoc, ← D.map_comp]
      exact congrArg (pullback.fst _ _ ≫ ·) (map_eq_map_of_preorder D _ _))
    (by rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd])

/-- The transition morphisms of the base changes over a tail commute with the second
projections to `Y₀`. -/
theorem tailBaseChange_map_snd {a b : {j : I // i₀ ≤ j}ᵒᵖ} (g : a ⟶ b) :
    (tailBaseChange D i₀ y).map g ≫ pullback.snd (D.map (homOfLE b.unop.2).op) y =
      pullback.snd (D.map (homOfLE a.unop.2).op) y :=
  pullback.lift_snd _ _ _

/-- The transition morphisms of the base changes over a tail lie over those of `D`. -/
theorem tailBaseChange_map_fst {a b : {j : I // i₀ ≤ j}ᵒᵖ} (g : a ⟶ b) :
    (tailBaseChange D i₀ y).map g ≫ pullback.fst (D.map (homOfLE b.unop.2).op) y =
      pullback.fst (D.map (homOfLE a.unop.2).op) y ≫
        D.map (homOfLE (show b.unop.1 ≤ a.unop.1 from leOfHom g.unop)).op :=
  pullback.lift_fst _ _ _

/-- The first projections `D_j ×_{D_{i₀}} Y₀ ⟶ D_j`. -/
abbrev tailBaseChangeFst : tailBaseChange D i₀ y ⟶ (tailInclusion i₀).op ⋙ D where
  app _ := pullback.fst _ _
  naturality _ _ g := tailBaseChange_map_fst D i₀ y g

/-- **The base changes over a tail have cartesian transition squares.** -/
theorem isPullback_tailBaseChange_map {a b : {j : I // i₀ ≤ j}ᵒᵖ} (g : a ⟶ b) :
    IsPullback ((tailBaseChange D i₀ y).map g) ((tailBaseChangeFst D i₀ y).app a)
      ((tailBaseChangeFst D i₀ y).app b)
      (D.map (homOfLE (show b.unop.1 ≤ a.unop.1 from leOfHom g.unop)).op) := by
  have h2 : D.map (homOfLE (show b.unop.1 ≤ a.unop.1 from leOfHom g.unop)).op ≫
      D.map (homOfLE b.unop.2).op = D.map (homOfLE a.unop.2).op := by
    rw [← D.map_comp]
    exact map_eq_map_of_preorder D _ _
  have s : IsPullback
      ((tailBaseChange D i₀ y).map g ≫ pullback.snd (D.map (homOfLE b.unop.2).op) y)
      (pullback.fst (D.map (homOfLE a.unop.2).op) y) y
      (D.map (homOfLE (show b.unop.1 ≤ a.unop.1 from leOfHom g.unop)).op ≫
        D.map (homOfLE b.unop.2).op) := by
    rw [tailBaseChange_map_snd, h2]
    exact (IsPullback.of_hasPullback (D.map (homOfLE a.unop.2).op) y).flip
  exact IsPullback.of_right s (tailBaseChange_map_fst D i₀ y g)
    (IsPullback.of_hasPullback (D.map (homOfLE b.unop.2).op) y).flip

variable {D i₀ y}

/-- The morphisms from a cone into the base changes over a tail, given a morphism into the cone
point and one into `Y₀` agreeing over the stage `i₀`. -/
abbrev tailBaseChangeLift (c : Cone D) {P : C} (m : P ⟶ c.pt) (q : P ⟶ Y₀)
    (h : q ≫ y = m ≫ c.π.app (op i₀)) :
    (Functor.const _).obj P ⟶ tailBaseChange D i₀ y where
  app j := pullback.lift (m ≫ c.π.app (op j.unop.1)) q (by rw [Category.assoc, c.w, h])
  naturality a b g := pullback.hom_ext (by
      simp only [Functor.const_obj_map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
      exact (Category.id_comp _).trans (congrArg (m ≫ ·) (c.w _).symm)) (by
      simp only [Functor.const_obj_map, Category.assoc, pullback.lift_snd]
      exact Category.id_comp _)

/-- **The base change of a cartesian square over a tail.** If `P = c.pt ×_{D_{i₀}} Y₀` then
`P = c.pt ×_{D_j} (D_j ×_{D_{i₀}} Y₀)` for every `j ≥ i₀`. -/
theorem isPullback_tailBaseChangeLift (c : Cone D) {P : C} (m : P ⟶ c.pt) (q : P ⟶ Y₀)
    (hpb : IsPullback q m y (c.π.app (op i₀))) (j : {j : I // i₀ ≤ j}ᵒᵖ) :
    IsPullback ((tailBaseChangeLift c m q hpb.w).app j) m ((tailBaseChangeFst D i₀ y).app j)
      (c.π.app (op j.unop.1)) := by
  have h1 : (tailBaseChangeLift c m q hpb.w).app j ≫
      pullback.snd (D.map (homOfLE j.unop.2).op) y = q := pullback.lift_snd _ _ _
  have s : IsPullback ((tailBaseChangeLift c m q hpb.w).app j ≫
      pullback.snd (D.map (homOfLE j.unop.2).op) y) m y
      (c.π.app (op j.unop.1) ≫ D.map (homOfLE j.unop.2).op) := by
    rw [h1, c.w]
    exact hpb
  exact IsPullback.of_right s (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (D.map (homOfLE j.unop.2).op) y).flip

end TailBaseChange

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "F" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

namespace ElementaryChart

variable {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}

/-- A cone over a system of presheaves over the stages of a Noetherian approximation, whose
components are the base changes of the limit cone, is a limit cone. -/
private def isLimitOfIsPullbackApproximation
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    {E : A.Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (pE : E ⟶ A.diagram)
    (c : Cone E) (f : (Cone.postcompose pE).obj c ⟶ Cone.mk X A.π)
    (hf : ∀ i, IsPullback (c.π.app i) f.hom (pE.app i) (A.π.app i)) : IsLimit c := by
  have := A.isCofiltered_op
  have := IsCofiltered.isConnected A.Iᵒᵖ
  exact isLimitOfIsPullbackOfIsConnected pE c _ f hf A.isLimit

/-- A system of presheaves with cartesian transition squares over the stages of a Noetherian
approximation has base changes bounded by the cutoff. -/
private theorem baseChangeSizeBounded_of_isPullback_approximation
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    {E : A.Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (pE : E ⟶ A.diagram)
    (hmap : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j),
      IsPullback (E.map g) (pE.app i) (pE.app j) (A.diagram.map g)) :
    BaseChangeSizeBounded B (⊤_ Scheme.{u}) hZ E :=
  @baseChangeSizeBounded_of_jointlyMono B _ hZ _ _ _ _ (𝟭 _) A.diagram _ pE
    (fun a _ _ _ h₁ h₂ => (hmap a).hom_ext h₁ h₂) A.isAlgebraicSpace
    (fun f => A.isAffineHom_map f) A.baseChangeSizeBounded

/-- **A W-system from a system of presheaves.** Let `U = lim U_i` be a Noetherian approximation of
the open part of an elementary chart, indexed below the cutoff, and let `E_i ⟶ U_i` be a system of
presheaves over the stages with cartesian transition squares `E_i = E_j ×_{U_j} U_i`, with
`W = E_i ×_{U_i} U` for every `i`, each `E_i ⟶ U_i` étale and each `E_i` quasi-compact and
representable. Then the representing objects form a W-system
(`AlgebraicGeometry.Space.ElementaryChart.WSystem`). The limit `W = lim W_i` holds in presheaves
because limits are stable under these base changes
(`CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected`), in the site because the Yoneda
embedding reflects limits, and in schemes because the system is bounded by the cutoff
(`AlgebraicGeometry.Space.nonempty_isLimit_toScheme_mapCone_of_baseChangeSizeBounded`). -/
theorem nonempty_wSystem_of_isRepresentable (C : ElementaryChart X V)
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor) (hA : #A.I < B.cutoff)
    (E : A.Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (pE : E ⟶ A.diagram)
    (wE : (Functor.const A.Iᵒᵖ).obj (yoneda.obj C.W) ⟶ E)
    (hrep : ∀ i, (E.obj i).IsRepresentable)
    (het : ∀ i, IsEtale B (⊤_ Scheme.{u}) hZ (pE.app i))
    (hmap : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j),
      IsPullback (E.map g) (pE.app i) (pE.app j) (A.diagram.map g))
    (hw : ∀ i, IsPullback (wE.app i) C.p (pE.app i) (A.π.app i))
    (hqc : ∀ i, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (E.obj i)) :
    Nonempty (C.WSystem A) := by
  classical
  have hG : ∀ i, yoneda.essImage (E.obj i) := fun i => ⟨(E.obj i).reprX, ⟨(E.obj i).reprW⟩⟩
  let Wd : A.Iᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ := Functor.essImage.liftFunctor E yoneda hG
  let ε : Wd ⋙ yoneda ≅ E := Functor.essImage.liftFunctorCompIso E yoneda hG
  let p : Wd ⋙ yoneda ⟶ A.diagram := ε.hom ≫ pE
  have hεn : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j),
      E.map g ≫ ε.inv.app j = ε.inv.app i ≫ yoneda.map (Wd.map g) := fun _ _ g =>
    ε.inv.naturality g
  have hwn : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j), wE.app i ≫ E.map g = wE.app j := fun _ _ g => by
    simpa using (wE.naturality g).symm
  let w : (Functor.const A.Iᵒᵖ).obj C.W ⟶ Wd :=
    { app := fun i => yoneda.preimage (wE.app i ≫ ε.inv.app i)
      naturality := fun i j g => yoneda.map_injective (by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.map_comp, Functor.map_preimage, Category.assoc]
        rw [← hεn g, ← Category.assoc, hwn g]) }
  have hyw : ∀ i, yoneda.map (w.app i) = wE.app i ≫ ε.inv.app i := fun i =>
    Functor.map_preimage _ _
  have hpmap : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j),
      IsPullback (yoneda.map (Wd.map g)) (p.app i) (p.app j) (A.diagram.map g) := fun i j g =>
    IsPullback.of_iso (hmap g) (ε.app i).symm (ε.app j).symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp [p]) (by simp [p]) (by simp)
  have hpw : ∀ i, IsPullback (yoneda.map (w.app i)) C.p (p.app i) (A.π.app i) := fun i =>
    IsPullback.of_iso (hw i) (Iso.refl _) (ε.app i).symm (Iso.refl _) (Iso.refl _)
      (by simp [hyw]) (by simp) (by simp [p]) (by simp)
  -- the limit `W = lim W_i`, in presheaves, in the site and in schemes
  have hlimY : IsLimit (yoneda.mapCone (Cone.mk C.W w)) :=
    isLimitOfIsPullbackApproximation A p (yoneda.mapCone (Cone.mk C.W w))
      ⟨C.p, fun i => (hpw i).w.symm⟩ hpw
  have hc : IsLimit (Cone.mk C.W w) := isLimitOfReflects yoneda hlimY
  have hAff : ∀ {i j : A.Iᵒᵖ} (g : i ⟶ j),
      IsAffineHom B (⊤_ Scheme.{u}) hZ ((Wd ⋙ yoneda).map g) := fun g =>
    IsAffineHom.of_isPullback (hpmap g).flip (A.isAffineHom_map g)
  have hB : BaseChangeSizeBounded B (⊤_ Scheme.{u}) hZ (Wd ⋙ yoneda) :=
    baseChangeSizeBounded_of_isPullback_approximation A p hpmap
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, -⟩ := A.isCutoffBoundedSystem B hA
  have hSL := nonempty_isLimit_toScheme_mapCone_of_baseChangeSizeBounded (Wd ⋙ yoneda) Wd
    (Iso.refl _) hSize hν hHomSize hB hAff hc
  exact ⟨{
    Wd := Wd
    p := p
    w := w
    etale_p := fun i => (isEtale_iff_presheaf_of_yoneda B _ hZ (p.app i)).1
      (isEtale_comp B _ hZ (isEtale_of_isIso B _ hZ _) (het i))
    isPullback_map := hpmap
    isPullback_w := hpw
    compactSpace := fun i => compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ
      (isQuasiCompactSpace_of_iso B _ hZ (ε.app i).symm (hqc i))
    isLimit := hSL.some }⟩

variable (B hZ) in
/-- **The W-systems of Stacks 07SU exist over approximations indexed below the cutoff.** Let
`f : V ⟶ X` be an elementary chart of a quasi-compact quasi-separated algebraic space over
`Spec ℤ`, with `V` quasi-compact and separated, open part `U` and `W = f⁻¹(U)`, and let
`U = lim U_i` be a Noetherian approximation indexed below the cutoff. Then a tail of it carries a
W-system (`AlgebraicGeometry.Space.ElementaryChart.WSystem`).

As in the source: `W ⟶ U` is étale and of finite presentation (it is a base change of `f`, which
is quasi-compact because `V` is and `X` is quasi-separated), so Stacks 07SK, for the system
`(U_i)`, which is bounded by the cutoff, descends it to `Y₀ ⟶ U_{i₀}` of finite presentation;
Stacks 07SL makes `Y₀ ×_{U_{i₀}} U_i ⟶ U_i` étale for `i ≥ i₁`; Stacks 07SR, applied to the system
`(Y₀ ×_{U_{i₀}} U_i)_{i ≥ i₀}` with limit `W`, makes one stage a scheme, and the later stages
are schemes because they are affine over it. The W-system lives over the tail above a common
upper bound of these stages. -/
theorem hasCutoffBoundedWSystems : HasCutoffBoundedWSystems B hZ := by
  intro X V C hX hqc hqs hVc hVsep hsurj hU ⟨A₀, hA₀⟩
  classical
  have := A₀.isCofiltered_op
  set D := A₀.diagram with hDdef
  have hD : IsCutoffBoundedSystem B _ hZ D := A₀.isCutoffBoundedSystem B hA₀
  have hDZ := fun j => isFinitePresentation_terminal_of_isFiniteType_viewOverIntegers
    (A₀.isAlgebraicSpace j) (A₀.isAbsolutelyQuasiSeparated j) (A₀.isFiniteTypeOverIntegers j)
  have hDqc : ∀ j, IsQuasiCompactSpace B _ hZ (D.obj j) := fun j => (hDZ j).2.1
  let eU : C.U.toFunctor ≅ limit D := A₀.isLimit.conePointUniqueUpToIso (limit.isLimit D)
  have heU : ∀ j, eU.hom ≫ limit.π D j = A₀.π.app j := fun j =>
    A₀.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D) j
  have hUalg : IsAlgebraicSpace B _ hZ C.U.toFunctor := hU.1
  have hlim : IsAlgebraicSpace B _ hZ (limit D) := isAlgebraicSpace_of_iso B _ hZ eU hUalg
  have hWalg := isAlgebraicSpace_yoneda B _ hZ C.W
  have hValg := isAlgebraicSpace_yoneda B _ hZ V
  -- `W ⟶ U` is étale and of finite presentation
  have := hVsep
  have hVqs : IsAbsolutelyQuasiSeparated B _ hZ hZ (yoneda.obj V) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ (yoneda.obj V) hZ
      ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩
  have hfet : IsEtale B _ hZ C.f := isEtale_of_presheaf_etale B _ hZ C.etale_f
  have hpet : IsEtale B _ hZ C.p :=
    isEtale_of_isPullback_of_isAlgebraicSpace B _ hZ C.isPullback_W.flip hWalg hUalg hValg hX hfet
  have hfqc : IsQuasiCompact B _ hZ C.f :=
    isQuasiCompact_of_isQuasiCompactSpace B _ hZ hZ hX hqs
      (isQuasiCompactSpace_yoneda_of_compactSpace B _ hZ V hVc) C.f
  have hpfp : IsFinitePresentation B _ hZ C.p :=
    ⟨isLocallyOfFinitePresentation_of_isEtale B _ hZ hpet,
      isQuasiCompact_of_isPullback B _ hZ C.isPullback_W hfqc,
      isQuasiSeparated_of_isPullback B _ hZ C.isPullback_W
        (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ hValg hVqs C.f)⟩
  have hYfp : IsFinitePresentation B _ hZ (C.p ≫ eU.hom) :=
    isFinitePresentation_of_arrowIso B _ hZ C.p (C.p ≫ eU.hom) (𝟙 _) eU.hom (by simp) hpfp
  -- Stacks 07SK: a model `Y₀ ⟶ U_{i₀}` of `W ⟶ U`
  obtain ⟨⟨i₀⟩, Y₀, hY₀, hY₀fp, ⟨e₀⟩⟩ :=
    IsCutoffBoundedSystem.exists_model_of_finitePresentation B _ hZ hZ D A₀.isAlgebraicSpace
      (fun g => A₀.isAffineHom_map g) hDqc A₀.isAbsolutelyQuasiSeparated hD
      (Over.mk (C.p ≫ eU.hom)) hWalg hYfp
  have hY₀qc : IsQuasiCompactSpace B _ hZ Y₀.left :=
    isQuasiCompactSpace_of_isFinitePresentation B _ hZ Y₀.hom (A₀.isAlgebraicSpace (op i₀))
      (hDqc (op i₀)) hY₀fp
  have hY₀qs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀.left :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hY₀
      (A₀.isAbsolutelyQuasiSeparated (op i₀)) hY₀fp.2.2
  set q₀ : yoneda.obj C.W ⟶ Y₀.left := e₀.hom.left ≫ pullback.fst Y₀.hom (limit.π D (op i₀))
    with hq₀
  have hsq₀ : IsPullback q₀ C.p Y₀.hom (A₀.π.app (op i₀)) := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback Y₀.hom (limit.π D (op i₀)))
      ((Over.forget _).mapIso e₀).symm (Iso.refl _) eU.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hq₀]
    · have h := Over.w e₀.inv
      simp only [Over.mk_hom, Over.pullback_obj_hom] at h
      rw [← h]
      simp
    · simp
    · simp [← heU]
  -- Stacks 07SL: the model is étale over a later stage
  have hfstL : IsEtale B _ hZ (pullback.fst (limit.π D (op i₀)) Y₀.hom) := by
    have h : pullback.fst (limit.π D (op i₀)) Y₀.hom =
        ((Over.forget _).mapIso e₀ ≪≫ pullbackSymmetry _ _).inv ≫ C.p ≫ eU.hom := by
      rw [Iso.eq_inv_comp]
      have h := Over.w e₀.hom
      simp only [Over.mk_hom, Over.pullback_obj_hom] at h
      simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
      rw [pullbackSymmetry_hom_comp_fst, h]
    rw [h]
    exact isEtale_comp B _ hZ (isEtale_of_isIso B _ hZ _)
      (isEtale_comp B _ hZ hpet (isEtale_of_isIso B _ hZ _))
  have hetL : IsEtale B _ hZ (pullback.map (limit.π D (op i₀)) Y₀.hom
      (limit.π D (op i₀)) (𝟙 _) (𝟙 _) Y₀.hom (𝟙 _) (by simp) (by simp)) := by
    have hm : pullback.map (limit.π D (op i₀)) Y₀.hom (limit.π D (op i₀)) (𝟙 _) (𝟙 _) Y₀.hom
        (𝟙 _) (by simp) (by simp) = pullback.fst (limit.π D (op i₀)) Y₀.hom ≫
          inv (pullback.fst (limit.π D (op i₀)) (𝟙 (D.obj (op i₀)))) := by
      rw [IsIso.eq_comp_inv]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hm]
    exact isEtale_comp B _ hZ hfstL (isEtale_of_isIso B _ hZ _)
  obtain ⟨i₁, hi₁, het₁⟩ := exists_isEtale_pullbackMap_of_isCutoffBoundedSystem B _ hZ hZ D hD
    (fun _ => A₀.isAlgebraicSpace _) (fun a => A₀.isAffineHom_map a) i₀ Y₀.hom (𝟙 _) Y₀.hom
    (Category.comp_id _) hY₀ (A₀.isAlgebraicSpace _) hY₀qc (hDqc _)
    (A₀.isAbsolutelyQuasiSeparated _) hY₀fp.1 hetL
  have hfst₁ : IsEtale B _ hZ (pullback.fst (D.map (homOfLE hi₁).op) Y₀.hom) := by
    have hfst : pullback.fst (D.map (homOfLE hi₁).op) Y₀.hom =
        pullback.map (D.map (homOfLE hi₁).op) Y₀.hom (D.map (homOfLE hi₁).op) (𝟙 _) (𝟙 _)
          Y₀.hom (𝟙 _) (by simp) (by simp) ≫ pullback.fst (D.map (homOfLE hi₁).op) (𝟙 _) := by
      simp
    rw [hfst]
    exact isEtale_comp B _ hZ het₁ (isEtale_of_isIso B _ hZ _)
  -- the system `E_j = U_j ×_{U_{i₀}} Y₀` over the tail above `i₀`
  have := isDirected_tail i₀
  let A₁ := A₀.tail i₀
  let E₁ := tailBaseChange D i₀ Y₀.hom
  let pE₁ : E₁ ⟶ A₁.diagram := tailBaseChangeFst D i₀ Y₀.hom
  let wE₁ : (Functor.const A₁.Iᵒᵖ).obj (yoneda.obj C.W) ⟶ E₁ :=
    tailBaseChangeLift (Cone.mk C.U.toFunctor A₀.π) C.p q₀ hsq₀.w
  have hmap₁ : ∀ ⦃a b : A₁.Iᵒᵖ⦄ (g : a ⟶ b),
      IsPullback (E₁.map g) (pE₁.app a) (pE₁.app b) (A₁.diagram.map g) := fun _ _ g =>
    isPullback_tailBaseChange_map D i₀ Y₀.hom g
  have hw₁ : ∀ a : A₁.Iᵒᵖ, IsPullback (wE₁.app a) C.p (pE₁.app a) (A₁.π.app a) := fun a =>
    isPullback_tailBaseChangeLift (Cone.mk C.U.toFunctor A₀.π) C.p q₀ hsq₀ a
  have hEalg : ∀ a : A₁.Iᵒᵖ, IsAlgebraicSpace B _ hZ (E₁.obj a) := fun _ =>
    isAlgebraicSpace_pullback B _ hZ _ _ (A₀.isAlgebraicSpace _) hY₀ (A₀.isAlgebraicSpace _)
  have hEqs : ∀ a : A₁.Iᵒᵖ, IsAbsolutelyQuasiSeparated B _ hZ hZ (E₁.obj a) := fun _ =>
    isAbsolutelyQuasiSeparated_pullback B _ hZ hZ _ _ (A₀.isAlgebraicSpace _) hY₀
      (A₀.isAlgebraicSpace _) (A₀.isAbsolutelyQuasiSeparated _) hY₀qs
  have hEfp : ∀ a : A₁.Iᵒᵖ, IsFinitePresentation B _ hZ (pE₁.app a) := fun a =>
    isFinitePresentation_of_arrowIso B _ hZ (pullback.snd Y₀.hom (D.map (homOfLE a.unop.2).op))
      (pullback.fst (D.map (homOfLE a.unop.2).op) Y₀.hom) (pullbackSymmetry _ _).hom (𝟙 _)
      (by rw [Category.comp_id]; exact pullbackSymmetry_hom_comp_fst _ _)
      (isFinitePresentation_pullback_snd B _ hZ Y₀.hom (D.map (homOfLE a.unop.2).op) hY₀
        (A₀.isAlgebraicSpace _) (A₀.isAlgebraicSpace _) hY₀fp)
  have hEqc : ∀ a : A₁.Iᵒᵖ, IsQuasiCompactSpace B _ hZ (E₁.obj a) := fun a =>
    isQuasiCompactSpace_of_isFinitePresentation B _ hZ (pE₁.app a) (A₀.isAlgebraicSpace _)
      (hDqc _) (hEfp a)
  have hEaff : ∀ ⦃a b : A₁.Iᵒᵖ⦄ (g : a ⟶ b), IsAffineHom B _ hZ (E₁.map g) := fun _ _ g =>
    IsAffineHom.of_isPullback (hmap₁ g).flip (A₁.isAffineHom_map g)
  -- Stacks 07SR: some stage is a scheme
  have hE₁c : IsCutoffBoundedSystem B _ hZ E₁ :=
    isCutoffBoundedSystem_of_preorder B _ hZ ((A₀.mk_tail_le i₀).trans_lt hA₀)
      (baseChangeSizeBounded_of_isPullback_approximation A₁ pE₁ hmap₁)
  let DS : DescentSituation B (⊤_ Scheme.{u}) hZ hZ A₁.I :=
    { system := E₁
      algebraicSpace := fun _ => hEalg _
      transition_affine := fun g => hEaff g
      quasiCompact := fun _ => hEqc _
      quasiSeparated := fun _ => hEqs _
      limitCone := Cone.mk (yoneda.obj C.W) wE₁
      isLimit := isLimitOfIsPullbackApproximation A₁ pE₁ (Cone.mk (yoneda.obj C.W) wE₁)
        ⟨C.p, fun a => (hw₁ a).w.symm⟩ hw₁
      limitAlgebraicSpace := hWalg
      base := ⟨i₀, le_rfl⟩ }
  obtain ⟨i₂, hi₂⟩ := DS.exists_isRepresentable_system_obj_of_isCutoffBoundedSystem hE₁c
    (show (yoneda.obj C.W).IsRepresentable from inferInstance)
  -- the tail above `i₂` and `i₁`
  obtain ⟨i₃, h₂₃, h₁₃⟩ := directed_of (· ≤ ·) i₂ (⟨i₁, hi₁⟩ : A₁.I)
  let A₂ := A₁.tail i₃
  have hA₂ : #A₂.I < B.cutoff :=
    ((A₁.mk_tail_le i₃).trans (A₀.mk_tail_le i₀)).trans_lt hA₀
  have : (E₁.obj (op i₂)).IsRepresentable := hi₂
  obtain ⟨WS⟩ := nonempty_wSystem_of_isRepresentable C A₂ hA₂ ((tailInclusion i₃).op ⋙ E₁)
    (Functor.whiskerLeft (tailInclusion i₃).op pE₁) (Functor.whiskerLeft (tailInclusion i₃).op wE₁)
    (fun a => isRepresentable_of_isAffineHom B _ hZ (E₁.map (homOfLE (h₂₃.trans a.unop.2)).op)
      (hEalg _) (hEalg _) (hEaff _))
    (fun a => isEtale_of_isPullback_of_isAlgebraicSpace B _ hZ
      (hmap₁ (homOfLE (h₁₃.trans a.unop.2)).op).flip (hEalg _) (A₀.isAlgebraicSpace _)
      (hEalg _) (A₀.isAlgebraicSpace _) hfst₁)
    (fun _ _ g => hmap₁ _) (fun a => hw₁ _) (fun a => hEqc _)
  exact ⟨A₂, hA₂, ⟨WS⟩⟩

end ElementaryChart

/-! ### Stacks 07SU and the assembly of Stacks 0A0X without the W-systems -/

/-- **Stacks 07SU over `Spec ℤ`, indexed below the cutoff.** Every quasi-compact quasi-separated
algebraic space over `Spec ℤ` has a Noetherian approximation whose index set has fewer elements
than the cutoff of the site. This is
`AlgebraicGeometry.Space.hasCutoffBoundedNoetherianApproximation_of_hasCutoffBoundedWSystems`
with the W-systems supplied by
`AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`. -/
theorem hasCutoffBoundedNoetherianApproximation_of_isQuasiCompactSpace
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    HasCutoffBoundedNoetherianApproximation B hZ X :=
  hasCutoffBoundedNoetherianApproximation_of_hasCutoffBoundedWSystems
    (ElementaryChart.hasCutoffBoundedWSystems B hZ) X hX hqc hqs

/-- **Stacks 07SU over `Spec ℤ` with a system bounded by the cutoff.** Every quasi-compact
quasi-separated algebraic space over `Spec ℤ` has a Noetherian approximation whose system is
bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`). This is
`AlgebraicGeometry.Space.exists_isCutoffBounded_noetherianApproximation` with the W-systems
supplied by `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`. -/
theorem exists_isCutoffBoundedSystem_noetherianApproximation
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X, letI := A.preorder;
      IsCutoffBoundedSystem B (⊤_ Scheme.{u}) hZ A.diagram :=
  exists_isCutoffBounded_noetherianApproximation (ElementaryChart.hasCutoffBoundedWSystems B hZ)
    X hX hqc hqs

variable (hZ) in
/-- **Stacks 0A0X under the cutoff bound, from Stacks 0A0W and 08K1.** This is
`Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedWSystems`
with its input `hW` supplied by `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`
and its input `h07SK` by
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation`. The remaining
inputs `h0A0W` (Stacks 0A0W) and `h08K1` (Stacks 08K1 for a system bounded by the cutoff) are those
of the original. There is no bound on the index set of the conclusion. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_isCutoffBoundedSystem
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) :=
  exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedWSystems hZ
    (ElementaryChart.hasCutoffBoundedWSystems B hZ) h0A0W
    (fun {_} _ _ D hC hD hA hQc hQs =>
      IsCutoffBoundedSystem.exists_model_of_finitePresentation B _ hZ hZ D hD hA hQc hQs hC)
    h08K1 hX hY f hf hYqc hYqs

variable (hZ) in
/-- **Stacks 0A0X over an affine target, in the shape the assembly of Stacks 0D3D consumes, from
Stacks 0A0W and 08K1.** This is
`Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_cutoffBoundedWSystems`
with its input `hW` supplied by `AlgebraicGeometry.Space.ElementaryChart.hasCutoffBoundedWSystems`
and its input `h07SK` by
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation`. The remaining
inputs `h0A0W` and `h08K1` are those of the original. -/
theorem exists_descentSituation_arrow_isCutoffBoundedSystem
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        IsCutoffBoundedSystem B _ hZ DX.system ∧ IsCutoffBoundedSystem B _ hZ DY.system :=
  exists_descentSituation_arrow_isCutoffBoundedSystem_of_cutoffBoundedWSystems hZ
    (ElementaryChart.hasCutoffBoundedWSystems B hZ) h0A0W
    (fun {_} _ _ D hC hD hA hQc hQs =>
      IsCutoffBoundedSystem.exists_model_of_finitePresentation B _ hZ hZ D hD hA hQc hQs hC)
    h08K1

end AlgebraicGeometry.Space

end
