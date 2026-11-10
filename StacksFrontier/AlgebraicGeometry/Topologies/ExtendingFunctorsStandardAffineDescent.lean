module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringLimitDescent

/-!
# Descent of a standard covering along a presentation of an affine object

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a) and (b). Stacks 0GDW deduces the
restricted sheaf condition `AlgebraicGeometry.ExtendingFunctors.IsStandardAffineSheaf` for the
extension of `F` from its condition (c) in three steps: an affine object `V` of `Sch/S` lying
over an affine open of `S` is written as a directed inverse limit `V = lim_m V_m` of affines of
finite presentation over an affine open of `S` (Stacks 00QN), a standard `τ`-covering
`{W_i ⟶ V}` is descended to a standard `τ`-covering `{W_{i,l} ⟶ V_l}` of one stage (Stacks
049N), and the sheaf condition is read off at the stages and passed to the filtered colimit.

This file carries out the first two steps and identifies each `W_i` with the limit of the
base-changed system `W_{i,m} = V_m ×_{V_l} W_{i,l}`, whose stages are again affine and of finite
presentation over the same affine open of `S`; consequently the value of the extension at `W_i`
is the filtered colimit of the values of `F` at the stages. This is the source's
`F'(W_i) = colim_m F(W_{i,m})`.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.toBottom`,
  `AlgebraicGeometry.ExtendingFunctors.overBottom`: the projections of a system indexed by the
  opposite of a poset with a least element to its least stage, and the system read as a system of
  objects over that stage.
* `AlgebraicGeometry.ExtendingFunctors.baseChange`,
  `AlgebraicGeometry.ExtendingFunctors.baseChangeCone`: the base change of such a system along a
  morphism into its least stage, and the base change of a cone on it.
* `AlgebraicGeometry.ExtendingFunctors.baseChangeToAffineOpen`: the factorization through an
  affine open of `S` of the structure morphism of a stage of a base-changed system.

## Main results

* `AlgebraicGeometry.finitePresentation_of_isStandardCovering`: every member of a standard
  `τ`-covering is of finite presentation, for each of the five topologies.
* `AlgebraicGeometry.ExtendingFunctors.exists_lfpPart_iso`: condition (2) of Stacks 0EUW in the
  form in which it is used, namely producing an object of the locally-finitely-presented part of
  the subcategory.
* `AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_finitePresentation`: Stacks 00QN
  with the finite presentation of the stages over a single affine open of `S` recorded, which is
  the data condition (c) asks of the target of a standard covering.
* `AlgebraicGeometry.ExtendingFunctors.isPullback_left`,
  `AlgebraicGeometry.ExtendingFunctors.exists_isoPullback_of_iso`: fibre products in `Sch/S` are
  computed on the underlying schemes, and an object of `Sch/S` identified with such a fibre
  product is the fibre product.
* `AlgebraicGeometry.ExtendingFunctors.exists_stage_standardCovering`: Stacks 049N (1) in
  `Sch/S`, a standard `τ`-covering of the limit being the base change of a standard
  `τ`-covering of a stage.
* `AlgebraicGeometry.ExtendingFunctors.isLimitBaseChangeCone`: the base change of a limit cone of
  connected shape is a limit cone.
* `AlgebraicGeometry.ExtendingFunctors.exists_lfpPart_iso_baseChange`: every stage of the
  base-changed system is an object of the subcategory up to isomorphism.
* `AlgebraicGeometry.ExtendingFunctors.nonempty_isColimit_extension_baseChange`: the extension
  carries the base-changed system to a filtered colimit.
* `AlgebraicGeometry.ExtendingFunctors.exists_baseChangePresentation_of_isStandardCovering`: the
  three preceding results assembled, for a standard `τ`-covering of an affine object lying over
  an affine open of `S`.

## Implementation notes

Base change along a fixed morphism is the right adjoint
`CategoryTheory.Over.mapPullbackAdj`, so it preserves limits; this is what makes the
base-changed system have the base-changed limit as its limit, and it is also why the base change
is defined as a composite of functors rather than stagewise. The forgetful functor of an over
category preserves limits of connected shape, and the opposite of a nonempty directed poset is
cofiltered, hence connected.

A presentation produced by
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_finitePresentation` is indexed by a
directed poset without a least element; the stage at which the covering is defined is made least
by restricting to the indices above it (`AlgebraicGeometry.ExtendingFunctors.iciIncl`), which
does not change the limit.

The five topologies are treated uniformly by quantifying over
`AlgebraicGeometry.CoveringTopology`; the only place where they are separated is the proof that
a member of a standard covering is locally of finite presentation.

## References

* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
* [Stacks Project, Tag 00QN](https://stacks.math.columbia.edu/tag/00QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v w u

/-! ### Members of a standard covering are of finite presentation -/

/-- A morphism with the property of morphisms defining one of the five topologies is locally of
finite presentation. -/
lemma locallyOfFinitePresentation_of_coveringMorphismProperty (τ : CoveringTopology)
    {X Y : Scheme.{u}} {g : X ⟶ Y} (h : coveringMorphismProperty τ g) :
    LocallyOfFinitePresentation g := by
  cases τ with
  | fppf => exact h.2
  | syntomic => exact AlgebraicGeometry.locallyOfFinitePresentation h
  | smooth => exact @instLocallyOfFinitePresentationOfSmooth _ _ g h
  | etale => exact @instLocallyOfFinitePresentationOfSmooth _ _ g (@Etale.instSmooth _ _ g h)
  | zariski => exact @locallyOfFinitePresentation_of_isOpenImmersion _ _ g h

/-- A morphism of affine schemes which is locally of finite presentation is of finite
presentation. -/
private lemma finitePresentation_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (hg : LocallyOfFinitePresentation g) : FinitePresentation g :=
  have := isAffineHom_of_isAffine g
  ⟨hg, inferInstance, inferInstance⟩

/-- **Every member of a standard `τ`-covering is of finite presentation.** The members are locally
of finite presentation because they have the property of morphisms defining the topology, and
quasi-compact and quasi-separated because their sources and target are affine. -/
lemma finitePresentation_of_isStandardCovering (τ : CoveringTopology) {T : Scheme.{u}}
    [IsAffine T] {ι : Type v} {U : ι → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (h : IsStandardCovering τ U f) (i : ι) : FinitePresentation (f i) := by
  have := h.affine_source i
  exact finitePresentation_of_isAffine (f i)
    (locallyOfFinitePresentation_of_coveringMorphismProperty τ
      (ExtendingFunctors.coveringMorphismProperty_of_isStandardCovering τ h i))

namespace ExtendingFunctors

variable {S : Scheme.{u}}

/-! ### Finite presentation: the closure properties used below -/

/-- Finite presentation is invariant under precomposition with an isomorphism. -/
lemma finitePresentation_isoComp {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {g : Y ⟶ Z}
    (hg : FinitePresentation g) : FinitePresentation (e ≫ g) :=
  have := hg.1
  have := hg.2.1
  have := hg.2.2
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Alias of `AlgebraicGeometry.FinitePresentation.comp`. -/
alias finitePresentation_comp := AlgebraicGeometry.FinitePresentation.comp

/-! ### Objects of the subcategory of finite presentation over an affine open -/

/-- An affine object of `Sch/S` whose structure morphism factors through an affine open of `S` by
a morphism of finite presentation is isomorphic to an object of the locally-finitely-presented
part of the subcategory. This is condition (2) of Stacks 0EUW in the form in which it is used:
the object produced by condition (2) is locally of finite presentation over `S` because it is
isomorphic, over `S`, to an object which is. -/
lemma exists_lfpPart_iso {P : ObjectProperty (Over S)} (hP : HasFinitePresentationAffines P)
    (U : S.affineOpens) (Z : Over S) (hZaff : IsAffine Z.left) (g : Z.left ⟶ U.1.toScheme)
    (hg : g ≫ U.1.ι = Z.hom) (hfp : FinitePresentation g) :
    ∃ Y : Over S, lfpPart P Y ∧ Nonempty (Z ≅ Y) := by
  obtain ⟨Y, hPY, ⟨i⟩⟩ := hP U Z.left g hZaff hfp
  have hZ : Z ≅ Over.mk (g ≫ U.1.ι) := Over.isoMk (Iso.refl Z.left) (by simpa using hg)
  refine ⟨Y, ⟨hPY, ?_⟩, ⟨hZ ≪≫ i⟩⟩
  have hw : i.inv.left ≫ (Over.mk (g ≫ U.1.ι)).hom = Y.hom := Over.w i.inv
  have hiso : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget S).map i.inv))
  have hlfpg : LocallyOfFinitePresentation g := hfp.1
  rw [← hw]
  exact inferInstanceAs (LocallyOfFinitePresentation (i.inv.left ≫ g ≫ U.1.ι))

/-! ### Presentations by objects of finite presentation over a fixed affine open -/

/-- **A presentation recording the finite presentation of its stages over a fixed affine open.**
An affine object of `Sch/S` lying over an affine open of `S` is a directed inverse limit of
affine objects of the subcategory which are locally of finite presentation over `S`, and the
structure morphism of each stage factors through a single affine open `U` of `S` by a morphism of
finite presentation.

This refines `AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation` by the data that
condition (c) of Stacks 0GDW asks of the target of a standard covering: the affine open `U` is
the one through which the structure morphism of the limit factors, and the approximating objects
are built from morphisms of finite presentation to it. -/
theorem exists_lfpPresentation_finitePresentation {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) (X : Over S) (hX : IsAffineOverAffineOpen X) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory)
      (π : (Functor.const Λᵒᵖ).obj X ⟶ D ⋙ (lfpPart P).ι) (_ : IsLimit (Cone.mk X π))
      (U : S.affineOpens) (g : ∀ l, (D.obj l).obj.left ⟶ U.1.toScheme),
      (∀ l, IsAffine (D.obj l).obj.left) ∧ (∀ l, g l ≫ U.1.ι = (D.obj l).obj.hom) ∧
        ∀ l, FinitePresentation (g l) := by
  classical
  obtain ⟨hXaff, U, gX, hgX⟩ := hX
  have : IsAffine X.left := hXaff
  have hUaff : IsAffine U.1.toScheme := U.2
  obtain ⟨Λ, _, _, _, D₀, c₀, hc₀, e, b, hDaff, hbfp, hfac⟩ :=
    Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_directedOrder_affine_limit_presentation gX
  let t : D₀ ⟶ (Functor.const Λᵒᵖ).obj S :=
    { app l := b.app l ≫ U.1.ι
      naturality := by
        intro l m h
        have hb := b.naturality h
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hb ⊢
        rw [← Category.assoc, hb] }
  let p : c₀.pt ⟶ S := e.inv ≫ X.hom
  have hp : ∀ l, c₀.π.app l ≫ t.app l = p := by
    intro l
    have h1 : e.inv ≫ gX = c₀.π.app l ≫ b.app l := by
      rw [hfac l, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    change c₀.π.app l ≫ b.app l ≫ U.1.ι = e.inv ≫ X.hom
    rw [← Category.assoc, ← h1, Category.assoc, hgX]
  have hfpb : ∀ l, FinitePresentation (b.app l) := by
    intro l
    have := hDaff l
    exact finitePresentation_of_isAffine (X := D₀.obj l) (Y := U.1.toScheme) (b.app l) (hbfp l)
  have hmem : ∀ l, ∃ Y : Over S, lfpPart P Y ∧
      Nonempty ((Over.lift D₀ t).obj l ≅ Y) := fun l =>
    exists_lfpPart_iso hP U ((Over.lift D₀ t).obj l) (hDaff l) (b.app l) rfl (hfpb l)
  choose Y hY hiso using hmem
  let ei : ∀ l, (Over.lift D₀ t).obj l ≅ Y l := fun l => (hiso l).some
  let α : Over.lift D₀ t ≅ (Over.lift D₀ t).copyObj Y ei :=
    Functor.isoCopyObj (Over.lift D₀ t) Y ei
  let c₁ : Cone ((lfpPart P).lift ((Over.lift D₀ t).copyObj Y ei) hY ⋙ (lfpPart P).ι) :=
    (Cone.postcompose α.hom).obj (Over.liftCone D₀ t c₀ p hp)
  have hc₁ : IsLimit c₁ :=
    (IsLimit.postcomposeHomEquiv α _).symm (Over.isLimitLiftCone D₀ t c₀ p hp hc₀)
  let ci : c₁.pt ≅ X := Over.isoMk e.symm rfl
  refine ⟨Λ, inferInstance, inferInstance, inferInstance,
    (lfpPart P).lift ((Over.lift D₀ t).copyObj Y ei) hY, (c₁.extend ci.inv).π,
    hc₁.ofIsoLimit (Cone.ext ci fun j => (Iso.hom_inv_id_assoc ci (c₁.π.app j)).symm),
    U, fun l => (ei l).inv.left ≫ b.app l, fun l => ?_, fun l => ?_, fun l => ?_⟩
  · have hl : IsAffine ((Over.lift D₀ t).obj l).left := hDaff l
    have eiso : (Y l).left ≅ ((Over.lift D₀ t).obj l).left :=
      ((Over.forget S).mapIso (ei l)).symm
    change IsAffine (Y l).left
    exact IsAffine.of_isIso eiso.hom
  · exact Over.w (ei l).inv
  · have hiso : IsIso (ei l).inv.left :=
      inferInstanceAs (IsIso ((Over.forget S).map (ei l).inv))
    exact finitePresentation_isoComp (ei l).inv.left (hfpb l)

/-! ### Fibre products in `Sch/S` -/

/-- **The forgetful functor to schemes preserves fibre products.** The shape of a fibre product is
connected, and the forgetful functor from `Sch/S` preserves connected limits. -/
lemma isPullback_left {A B C : Over S} (a : B ⟶ A) (b : C ⟶ A) :
    IsPullback (Limits.pullback.fst a b).left (Limits.pullback.snd a b).left a.left b.left :=
  (IsPullback.of_hasPullback a b).map (Over.forget S)

/-- A fibre product of affine objects of `Sch/S` over an affine object is affine. -/
lemma isAffine_pullback_left {A B C : Over S} (a : B ⟶ A) (b : C ⟶ A) (hA : IsAffine A.left)
    (hB : IsAffine B.left) (hC : IsAffine C.left) : IsAffine (Limits.pullback a b).left :=
  have := hA
  have := hB
  have := hC
  IsAffine.of_isIso (isPullback_left a b).isoPullback.hom

/-- **Recognizing a fibre product of `Sch/S` from the underlying schemes.** An object `Z` of
`Sch/S` over `B`, whose underlying scheme is identified with the fibre product of the underlying
schemes of `b : C ⟶ A` and `a : B ⟶ A` compatibly with the morphism to `B`, is the fibre product
of `a` and `b` in `Sch/S`. -/
lemma exists_isoPullback_of_iso {A B C : Over S} (a : B ⟶ A) (b : C ⟶ A) {Z : Over S}
    (p : Z ⟶ B) (θ : Limits.pullback b.left a.left ≅ Z.left)
    (hθ : θ.hom ≫ p.left = Limits.pullback.snd b.left a.left) :
    ∃ e : Z ≅ Limits.pullback a b, e.hom ≫ Limits.pullback.fst a b = p := by
  have hpb : IsPullback (Limits.pullback.snd a b).left (Limits.pullback.fst a b).left
      b.left a.left := (isPullback_left a b).flip
  have hψ : (hpb.isoPullback ≪≫ θ).hom ≫ p.left = (Limits.pullback.fst a b).left := by
    rw [Iso.trans_hom, Category.assoc, hθ, hpb.isoPullback_hom_snd]
  have hcond : (hpb.isoPullback ≪≫ θ).hom ≫ Z.hom = (Limits.pullback a b).hom := by
    rw [← Over.w p, ← Category.assoc, hψ]
    exact Over.w (Limits.pullback.fst a b)
  refine ⟨(Over.isoMk (hpb.isoPullback ≪≫ θ) hcond).symm, ?_⟩
  refine Over.OverMorphism.ext ?_
  have hinv : ((Over.isoMk (hpb.isoPullback ≪≫ θ) hcond).symm.hom).left
      = (hpb.isoPullback ≪≫ θ).inv := rfl
  have hcomp := congrArg (fun k => (hpb.isoPullback ≪≫ θ).inv ≫ k) hψ
  rw [Over.comp_left, hinv, ← hcomp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-! ### The descent of a standard covering to a stage of a presentation -/

/-- **A standard covering of a directed limit comes from a stage, read in `Sch/S`.** Let `V` be an
affine object of `Sch/S` written as the limit of a directed inverse system of affine objects of
the subcategory, and let `{W i ⟶ V}` be a standard `τ`-covering. Then over some stage `V_l` of
the system there is a standard `τ`-covering `{T i ⟶ V_l}` in `Sch/S` whose base change along the
projection `V ⟶ V_l` is the given covering.

This is `AlgebraicGeometry.exists_isStandardCovering_of_isLimit`, which is Stacks 049N (1),
transported from schemes to `Sch/S`: the underlying cone of schemes of the presentation is a
limit cone, the covering descended there is lifted back to `Sch/S` by composing with the
structure morphism of the stage, and the identification of the base change with the given
covering is read off from the corresponding identification of schemes, the two fibre products
agreeing because the forgetful functor preserves them. -/
theorem exists_stage_standardCovering (τ : CoveringTopology) {P : ObjectProperty (Over S)}
    {V : Over S} (hV : IsAffine V.left) {Λ : Type u} [PartialOrder Λ] [Nonempty Λ]
    [IsDirectedOrder Λ] {D : Λᵒᵖ ⥤ (lfpPart P).FullSubcategory}
    (π : (Functor.const Λᵒᵖ).obj V ⟶ D ⋙ (lfpPart P).ι) (hπ : IsLimit (Cone.mk V π))
    (haff : ∀ l, IsAffine (D.obj l).obj.left) {ι : Type v} (W : ι → Over S) (f : ∀ i, W i ⟶ V)
    (hstd : @IsStandardCovering τ V.left hV ι (fun i => (W i).left) (fun i => (f i).left)) :
    ∃ (l : Λᵒᵖ) (T : ι → Over S) (s : ∀ i, T i ⟶ (D.obj l).obj),
      (@IsStandardCovering τ (D.obj l).obj.left (haff l) ι (fun i => (T i).left)
          (fun i => (s i).left)) ∧
        ∀ i, ∃ e : W i ≅ Limits.pullback (π.app l) (s i),
          e.hom ≫ Limits.pullback.fst (π.app l) (s i) = f i := by
  classical
  have hVpt : IsAffine ((Over.forget S).mapCone (Cone.mk V π)).pt := hV
  have hDpt : ∀ l, IsAffine (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj l) := haff
  have hcone : IsLimit ((Over.forget S).mapCone (Cone.mk V π)) :=
    isLimitMapConeForgetOfDirected hπ
  obtain ⟨l, Tₛ, fₛ, hfₛ, he⟩ := exists_isStandardCovering_of_isLimit τ
    ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone (Cone.mk V π)) hcone
    (fun i => (W i).left) (fun i => (f i).left) hstd
  refine ⟨l, fun i => Over.mk (fₛ i ≫ (D.obj l).obj.hom),
    fun i => Over.homMk (fₛ i) rfl, hfₛ, fun i => ?_⟩
  obtain ⟨σ⟩ := he i
  exact exists_isoPullback_of_iso (π.app l)
    (Over.homMk (fₛ i) rfl : Over.mk (fₛ i ≫ (D.obj l).obj.hom) ⟶ (D.obj l).obj) (f i)
    ((Over.forget V.left).mapIso σ) (Over.w σ.hom)

/-! ### Base change of a system along a morphism into its least stage -/

section BaseChange

variable {Λ : Type u} [PartialOrder Λ] [OrderBot Λ]

/-- The projections of a system indexed by the opposite of a poset with a least element to its
least stage. -/
def toBottom (E : Λᵒᵖ ⥤ Over S) : E ⟶ (Functor.const Λᵒᵖ).obj (E.obj (op (⊥ : Λ))) where
  app m := E.map (homOfLE (bot_le : (⊥ : Λ) ≤ m.unop)).op
  naturality := by
    intro m n φ
    have h : φ ≫ (homOfLE (bot_le : (⊥ : Λ) ≤ n.unop)).op
        = (homOfLE (bot_le : (⊥ : Λ) ≤ m.unop)).op := Subsingleton.elim _ _
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← E.map_comp, h]

/-- A cone over a system, composed with the projection of a stage to the least stage, is the leg
of the cone at the least stage. -/
lemma toBottom_app_fac (E : Λᵒᵖ ⥤ Over S) (c : Cone E) (m : Λᵒᵖ) :
    c.π.app m ≫ (toBottom E).app m = c.π.app (op (⊥ : Λ)) :=
  c.w _

/-- A system indexed by the opposite of a poset with a least element, read as a system of objects
over its least stage. -/
@[implicit_reducible]
noncomputable def overBottom (E : Λᵒᵖ ⥤ Over S) : Λᵒᵖ ⥤ Over (E.obj (op (⊥ : Λ))) :=
  Over.lift E (toBottom E)

/-- **The base change of a system along a morphism into its least stage.** The stage `m` of the
base change of `E` along `t : T ⟶ E_⊥` is the fibre product `E_m ×_{E_⊥} T`. -/
@[implicit_reducible]
noncomputable def baseChange (E : Λᵒᵖ ⥤ Over S) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ))) :
    Λᵒᵖ ⥤ Over S :=
  overBottom E ⋙ Over.pullback t ⋙ Over.forget T

/-- The stage `m` of the base change of `E` along `t` is the fibre product of the projection
`E_m ⟶ E_⊥` with `t`. -/
lemma baseChange_obj (E : Λᵒᵖ ⥤ Over S) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ))) (m : Λᵒᵖ) :
    (baseChange E t).obj m = Limits.pullback ((toBottom E).app m) t :=
  rfl

/-- The cone of the base-changed system whose apex is the base change of the apex. -/
noncomputable def baseChangeCone (E : Λᵒᵖ ⥤ Over S) {T : Over S}
    (t : T ⟶ E.obj (op (⊥ : Λ))) (c : Cone E) : Cone (baseChange E t) :=
  (Over.forget T).mapCone ((Over.pullback t).mapCone
    (Over.liftCone E (toBottom E) c (c.π.app (op (⊥ : Λ))) (toBottom_app_fac E c)))

/-- The apex of the base-changed cone is the fibre product of the leg of `c` at the least stage
with `t`. -/
lemma baseChangeCone_pt (E : Λᵒᵖ ⥤ Over S) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))
    (c : Cone E) : (baseChangeCone E t c).pt = Limits.pullback (c.π.app (op (⊥ : Λ))) t :=
  rfl

/-- **The base change of a limit cone is a limit cone.** Base change along a fixed morphism is a
right adjoint, hence preserves limits, and the forgetful functor of an over category preserves
connected limits; the opposite of a nonempty directed poset is connected, being cofiltered. -/
noncomputable def isLimitBaseChangeCone [IsDirectedOrder Λ] (E : Λᵒᵖ ⥤ Over S) {T : Over S}
    (t : T ⟶ E.obj (op (⊥ : Λ))) (c : Cone E) (hc : IsLimit c) :
    IsLimit (baseChangeCone E t c) :=
  have : Nonempty Λᵒᵖ := ⟨op (⊥ : Λ)⟩
  have : IsConnected Λᵒᵖ := IsCofiltered.isConnected Λᵒᵖ
  isLimitOfPreserves (Over.forget T) (isLimitOfPreserves (Over.pullback t)
    (Over.isLimitLiftCone E (toBottom E) c (c.π.app (op (⊥ : Λ)))
      (toBottom_app_fac E c) hc))

/-- Every stage of the base change of a system of affine objects along a morphism out of an
affine object is affine. -/
lemma isAffine_baseChange_obj (E : Λᵒᵖ ⥤ Over S) (hE : ∀ m, IsAffine (E.obj m).left)
    {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ))) (hT : IsAffine T.left) (m : Λᵒᵖ) :
    IsAffine ((baseChange E t).obj m).left :=
  isAffine_pullback_left ((toBottom E).app m) t (hE _) (hE m) hT

/-- The factorization through the affine open `U` of `S` of the structure morphism of a stage of
a base-changed system: the projection to the stage of the original system, followed by its own
factorization. -/
noncomputable def baseChangeToAffineOpen (E : Λᵒᵖ ⥤ Over S) {U : S.affineOpens}
    (g : ∀ m, (E.obj m).left ⟶ U.1.toScheme) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))
    (m : Λᵒᵖ) : ((baseChange E t).obj m).left ⟶ U.1.toScheme :=
  (Limits.pullback.fst ((toBottom E).app m) t).left ≫ g m

/-- The factorization `baseChangeToAffineOpen E g t m`, followed by the inclusion of `U`, is the
structure morphism of the stage `m` of the base-changed system. -/
lemma baseChangeToAffineOpen_comp_ι (E : Λᵒᵖ ⥤ Over S) {U : S.affineOpens}
    (g : ∀ m, (E.obj m).left ⟶ U.1.toScheme) (hgU : ∀ m, g m ≫ U.1.ι = (E.obj m).hom)
    {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ))) (m : Λᵒᵖ) :
    baseChangeToAffineOpen E g t m ≫ U.1.ι = ((baseChange E t).obj m).hom := by
  change ((Limits.pullback.fst ((toBottom E).app m) t).left ≫ g m) ≫ U.1.ι
      = ((baseChange E t).obj m).hom
  rw [Category.assoc, hgU m]
  exact Over.w (Limits.pullback.fst ((toBottom E).app m) t)

/-- If each `g m` and `t` are of finite presentation, then so is the factorization
`baseChangeToAffineOpen E g t m` through `U`. -/
lemma finitePresentation_baseChangeToAffineOpen (E : Λᵒᵖ ⥤ Over S) {U : S.affineOpens}
    (g : ∀ m, (E.obj m).left ⟶ U.1.toScheme) (hgfp : ∀ m, FinitePresentation (g m))
    {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ))) (htfp : FinitePresentation t.left) (m : Λᵒᵖ) :
    FinitePresentation (baseChangeToAffineOpen E g t m) :=
  have hpb := (isPullback_left ((toBottom E).app m) t).flip
  finitePresentation_comp
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb htfp.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb htfp.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb htfp.2.2⟩ (hgfp m)

/-- **Every stage of a base-changed system is an object of the subcategory up to isomorphism.**
The stages of the base change of a presentation along a morphism of finite presentation out of an
affine object are affine and of finite presentation over the same affine open of `S` as the
stages of the presentation, so condition (2) of Stacks 0EUW applies to each of them. -/
theorem exists_lfpPart_iso_baseChange {P : ObjectProperty (Over S)}
    (hP : HasFinitePresentationAffines P) (E : Λᵒᵖ ⥤ Over S)
    (hE : ∀ m, IsAffine (E.obj m).left) (U : S.affineOpens)
    (g : ∀ m, (E.obj m).left ⟶ U.1.toScheme) (hgU : ∀ m, g m ≫ U.1.ι = (E.obj m).hom)
    (hgfp : ∀ m, FinitePresentation (g m)) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))
    (hT : IsAffine T.left) (htfp : FinitePresentation t.left) (m : Λᵒᵖ) :
    ∃ Y : Over S, lfpPart P Y ∧ Nonempty ((baseChange E t).obj m ≅ Y) :=
  exists_lfpPart_iso hP U ((baseChange E t).obj m)
    (isAffine_baseChange_obj E hE t hT m) (baseChangeToAffineOpen E g t m)
    (baseChangeToAffineOpen_comp_ι E g hgU t m)
    (finitePresentation_baseChangeToAffineOpen E g hgfp t htfp m)

/-- **The sections of the extension over the base change of a presentation form a filtered
colimit over the stages.** This is step (b) of the deduction of the restricted sheaf condition
from condition (c) in Stacks 0GDW: the member `W_i` of a standard covering of `V` is the inverse
limit of the base changes `W_{i,m} = V_m ×_{V_l} W_{i,l}` of the member of the descended
covering, every stage is affine, and the extension carries a directed inverse limit of affine
objects to a filtered colimit.

Together with
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPart_iso_baseChange`, which puts every stage in
the subcategory, this identifies the value of the extension at `W_i` with `colim_m F(W_{i,m})`,
the source's description of it. -/
theorem nonempty_isColimit_extension_baseChange [IsDirectedOrder Λ]
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (E : Λᵒᵖ ⥤ Over S)
    (hE : ∀ m, IsAffine (E.obj m).left) {T : Over S} (t : T ⟶ E.obj (op (⊥ : Λ)))
    (hT : IsAffine T.left) (c : Cone E) (hc : IsLimit c) :
    Nonempty (IsColimit ((extension P F).mapCocone (baseChangeCone E t c).op)) :=
  have : Nonempty Λ := ⟨⊥⟩
  preservesAffineLimits_extension F hP1 hP2 haF Λ (baseChange E t)
    (isAffine_baseChange_obj E hE t hT) (baseChangeCone E t c)
    (isLimitBaseChangeCone E t c hc)

end BaseChange

/-! ### The base-changed presentation of a standard covering -/

/-- **Step (b) of the deduction of the restricted sheaf condition in Stacks 0GDW.** Let `V` be an
affine object of `Sch/S` lying over an affine open of `S` and let `{W i ⟶ V}` be a standard
`τ`-covering. Then `V` is the limit of a directed inverse system `E` with a least stage, every
stage being an object of the locally-finitely-presented part of the subcategory which is affine
and of finite presentation over one affine open `U` of `S`; there is a standard `τ`-covering
`{T i ⟶ E_⊥}` of the least stage; and each `W i` is the base change of `T i` along the
projection `V ⟶ E_⊥`, so that `W i` is the limit of the base-changed system `baseChange E (s i)`,
whose stages are again affine and of finite presentation over `U`
(`AlgebraicGeometry.ExtendingFunctors.exists_lfpPart_iso_baseChange`) and at which the extension
is therefore computed by `F`
(`AlgebraicGeometry.ExtendingFunctors.nonempty_isColimit_extension_baseChange`).

This is the source's `W_i = lim_m (V_m ×_{V_l} W_{i,l})`. The least stage is produced by
restricting the presentation to the indices above the stage at which the covering is defined,
which does not change the limit. -/
theorem exists_baseChangePresentation_of_isStandardCovering (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (hP2 : HasFinitePresentationAffines P) {V : Over S}
    (hV : IsAffineOverAffineOpen V) {ι : Type v} (W : ι → Over S) (f : ∀ i, W i ⟶ V)
    (hstd : @IsStandardCovering τ V.left hV.1 ι (fun i => (W i).left) (fun i => (f i).left)) :
    ∃ (M : Type u) (_ : PartialOrder M) (_ : OrderBot M) (_ : IsDirectedOrder M)
      (E : Mᵒᵖ ⥤ Over S) (haff : ∀ m, IsAffine (E.obj m).left)
      (π : (Functor.const Mᵒᵖ).obj V ⟶ E) (_ : IsLimit (Cone.mk V π)) (U : S.affineOpens)
      (g : ∀ m, (E.obj m).left ⟶ U.1.toScheme) (T : ι → Over S)
      (s : ∀ i, T i ⟶ E.obj (op (⊥ : M))),
      (∀ m, lfpPart P (E.obj m)) ∧ (∀ m, g m ≫ U.1.ι = (E.obj m).hom) ∧
        (∀ m, FinitePresentation (g m)) ∧
        (@IsStandardCovering τ (E.obj (op (⊥ : M))).left (haff _) ι (fun i => (T i).left)
          (fun i => (s i).left)) ∧
        ∀ i, ∃ e : W i ≅ (baseChangeCone E (s i) (Cone.mk V π)).pt,
          e.hom ≫ Limits.pullback.fst (π.app (op (⊥ : M))) (s i) = f i := by
  classical
  obtain ⟨Λ, _, _, _, D, π₀, hπ₀, U, g₀, haff₀, hgU₀, hgfp₀⟩ :=
    exists_lfpPresentation_finitePresentation hP2 V hV
  obtain ⟨l, T, s, hTstd, hWiso⟩ :=
    exists_stage_standardCovering τ hV.1 π₀ hπ₀ haff₀ W f hstd
  exact ⟨↥(Set.Ici l.unop), inferInstance, Set.Ici.orderBot, isDirectedOrder_Ici l.unop,
    (iciIncl l.unop).op ⋙ D ⋙ (lfpPart P).ι, fun m => haff₀ _,
    (Cone.whisker (iciIncl l.unop).op (Cone.mk V π₀)).π,
    isLimitWhiskerIciIncl l.unop (Cone.mk V π₀) hπ₀, U, fun m => g₀ _, T, s,
    fun m => (D.obj _).property, fun m => hgU₀ _, fun m => hgfp₀ _, hTstd, hWiso⟩

end ExtendingFunctors

end AlgebraicGeometry

end
