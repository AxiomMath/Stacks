module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.FiniteTypeSchemes
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Countable families of fibrewise isomorphisms

Let `S` be a scheme of finite type over a field `K` and let `X ⟶ S` and `Y ⟶ S` be morphisms of
finite type. There is a countable set `I` and for each `i ∈ I` a finite-type morphism `Sᵢ ⟶ S`
together with an isomorphism `X ×_S Sᵢ ≅ Y ×_S Sᵢ` over `Sᵢ`, such that every `K`-point `s` of
`S` whose fibres `X_s` and `Y_s` are isomorphic over `K` factors through one of the `Sᵢ ⟶ S`.
When `K` is algebraically closed and `S` is of finite type over `K`, the `K`-points of `S` are
exactly its closed points.

## Main results

* `AlgebraicGeometry.exists_countable_finiteType_isomorphism_families`: the countable family of
  finite-type base changes carrying an isomorphism of the two base-changed schemes, detecting
  every `K`-point of the base at which the two fibres are isomorphic.
* `AlgebraicGeometry.exists_countable_finiteType_isomorphism_families_of_isAlgClosed`: the same
  statement over an algebraically closed field.

## Implementation notes

A scheme over a base is an object of `CategoryTheory.Over`, and a base change along a morphism of
bases is `CategoryTheory.Over.pullback`. A `K`-point of `S` is a morphism
`Over.mk (𝟙 (Spec K)) ⟶ S` of schemes over `K`; the fibre of `X` at such a point is the base
change of `X` along the underlying morphism `Spec K ⟶ S`. Finite type of a morphism is
`AlgebraicGeometry.LocallyOfFiniteType` together with `AlgebraicGeometry.QuasiCompact`.

## References

* [Stacks Project, Tag 0G0X](https://stacks.math.columbia.edu/tag/0G0X)
* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The finitely generated `ℤ`-subalgebras of a commutative ring, ordered by inclusion. -/
private abbrev FinGenSubalgebraIndex (K : Type u) [CommRing K] :=
  {A : Subalgebra ℤ K // A.FG}

/-- The finitely generated `ℤ`-subalgebras of a commutative ring form a filtered poset. -/
private theorem finGenSubalgebraIndex_isFiltered
    (K : Type u) [CommRing K] : IsFiltered (FinGenSubalgebraIndex K) where
  cocone_objs := by
    intro A B
    let C : FinGenSubalgebraIndex K := ⟨A.1 ⊔ B.1, Subalgebra.FG.sup A.2 B.2⟩
    refine ⟨C, homOfLE (show A ≤ C from by change A.1 ≤ C.1; exact le_sup_left),
      homOfLE (show B ≤ C from by change B.1 ≤ C.1; exact le_sup_right), trivial⟩
  cocone_maps := fun A B f g => ⟨B, 𝟙 B, Subsingleton.elim _ _⟩
  nonempty := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram of finitely generated `ℤ`-subalgebras of a commutative ring and the inclusions
between them. -/
private noncomputable def finGenSubalgebraDiagram (K : Type u) [CommRing K] :
    FinGenSubalgebraIndex K ⥤ CommRingCat where
  obj A := CommRingCat.of A.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The ring itself, with the inclusions of its finitely generated `ℤ`-subalgebras, is a cocone
on the diagram of those subalgebras. -/
private noncomputable def finGenSubalgebraCocone (K : Type u) [CommRing K] :
    Cocone (finGenSubalgebraDiagram K) where
  pt := CommRingCat.of K
  ι := {
    app A := CommRingCat.ofHom A.1.val.toRingHom
    naturality _ _ _ := by ext x; rfl
  }

/-- A finitely generated `ℤ`-subalgebra of a commutative ring is countable. -/
private theorem countable_fg_subalgebra {K : Type u} [CommRing K]
    (A : Subalgebra ℤ K) (hA : A.FG) : Countable (↑A : Type u) := by
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp hA
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ A).FG)
  have : Countable (↑s : Type u) := s.finite_toSet.countable.to_subtype
  have : Countable (MvPolynomial (↑s : Type u) ℤ) :=
    show Countable (AddMonoidAlgebra ℤ ((↑s : Type u) →₀ ℕ)) from inferInstance
  let φ : MvPolynomial (↑s : Type u) ℤ →ₐ[ℤ] A :=
    MvPolynomial.aeval (fun x : ↑s => (x : A))
  have hφ : φ.range = ⊤ := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe_subtype, Finset.setOfPred_mem,
      hs]
  exact ((AlgHom.range_eq_top φ).mp hφ).countable

/-- A commutative ring is the filtered colimit of its finitely generated `ℤ`-subalgebras. -/
private noncomputable def finGenSubalgebraCocone_isColimit (K : Type u) [CommRing K] :
    IsColimit (finGenSubalgebraCocone K) := by
  classical
  let I := FinGenSubalgebraIndex K
  let D := finGenSubalgebraDiagram K
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsFiltered I := finGenSubalgebraIndex_isFiltered K
  let A : I → Subalgebra ℤ K := fun i => i.1
  have dir : Directed (· ≤ ·) A := by
    intro i j
    change ∃ l : I, i ≤ l ∧ j ≤ l
    exact (IsFiltered.isDirectedOrder I).directed i j
  have hmem (x : K) : ∃ i : I, x ∈ A i :=
    ⟨⟨Algebra.adjoin ℤ {x}, (Subalgebra.fg_iff_finiteType _).2
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))⟩,
      Algebra.subset_adjoin (by simp)⟩
  have htop : (⨆ i, A i) = ⊤ := by
    apply le_antisymm
    · exact iSup_le fun _ => le_top
    · intro x hx
      change x ∈ ((⨆ i, A i : Subalgebra ℤ K) : Set K)
      rw [Subalgebra.coe_iSup_of_directed (K := A) dir]
      exact Set.mem_iUnion.mpr (hmem x)
  let f (c : Cocone D) (i : I) : A i →ₐ[ℤ] (↑c.pt) :=
    (c.ι.app i).hom.toIntAlgHom
  have hf (c : Cocone D) (i j : I) (h : A i ≤ A j) :
      f c i = (f c j).comp (Subalgebra.inclusion h) := by
    apply AlgHom.ext
    intro x
    change (c.ι.app i).hom x =
      (c.ι.app j).hom ((Subalgebra.inclusion h) x)
    have hc : D.map (homOfLE h) ≫ c.ι.app j = c.ι.app i := c.w (homOfLE h)
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom x) hc.symm
  let liftTop (c : Cocone D) :
      (↑(⊤ : Subalgebra ℤ K)) →ₐ[ℤ] (↑c.pt) :=
    Subalgebra.iSupLift A dir (f c) (hf c) ⊤ (by rw [htop])
  let desc (c : Cocone D) : CommRingCat.of K ⟶ c.pt :=
    CommRingCat.ofHom (liftTop c |>.comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom
  refine IsColimit.mk desc ?_ ?_
  · intro c i
    apply CommRingCat.hom_ext
    ext x
    change liftTop c (Subalgebra.topEquiv.symm x.1) = f c i x
    have htopI : Subalgebra.topEquiv.symm x.1 =
        Subalgebra.inclusion (show A i ≤ ⊤ from le_top) x :=
      Subtype.ext rfl
    rw [htopI]
    exact Subalgebra.iSupLift_inclusion (K := A) (dir := dir) (f := f c)
      (hf := hf c) (T := ⊤) (hT := by rw [htop]) (i := i) (x := x) (h := le_top)
  · intro c m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    let xK : K := x
    obtain ⟨i, hxT⟩ := hmem xK
    let xi : A i := ⟨xK, hxT⟩
    have hmEval := congrArg (fun q : CommRingCat.Hom _ _ => q.hom xi) (hm i)
    have h₁ : m.hom x = f c i xi := hmEval
    have h₂ : (desc c).hom x = f c i xi := by
      change liftTop c ((Subalgebra.topEquiv (R := ℤ) (A := K)).symm xK) = f c i xi
      have hmem : ((Subalgebra.topEquiv (R := ℤ) (A := K)).symm xK : K) ∈ A i := hxT
      exact Subalgebra.iSupLift_of_mem (K := A) (dir := dir) (f := f c) (hf := hf c)
        (T := ⊤) (hT := by rw [htop]) (i := i)
        (x := (Subalgebra.topEquiv (R := ℤ) (A := K)).symm xK) hmem
    exact h₁.trans h₂.symm

/-- Base changes along two equal morphisms of bases agree. -/
private noncomputable def overPullbackCongr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (A : Over Y) :
    (Over.pullback f).obj A ≅ (Over.pullback g).obj A := by
  cases h; exact Iso.refl _

/-- The base change of a morphism of finite presentation is of finite presentation. -/
private theorem finitePresentation_overPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A : Over Y) (hA : AlgebraicGeometry.FinitePresentation A.hom) :
    AlgebraicGeometry.FinitePresentation ((Over.pullback f).obj A).hom := by
  have : LocallyOfFinitePresentation A.hom := hA.1
  have : QuasiCompact A.hom := hA.2.1
  have : QuasiSeparated A.hom := hA.2.2
  refine ⟨?_, ?_, ?_⟩
  · change LocallyOfFinitePresentation (Limits.pullback.snd A.hom f)
    infer_instance
  · change QuasiCompact (Limits.pullback.snd A.hom f)
    infer_instance
  · change QuasiSeparated (Limits.pullback.snd A.hom f)
    infer_instance

/-- Two schemes of finite presentation over the limit of a cofiltered system of quasi-compact,
quasi-separated schemes with affine transitions are base changes of schemes of finite
presentation over one common stage. -/
private theorem exists_common_models
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (X Y : Over c.pt) (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom) :
    ∃ (i : J) (X₀ Y₀ : Over (D.obj i)),
      AlgebraicGeometry.FinitePresentation X₀.hom ∧
      AlgebraicGeometry.FinitePresentation Y₀.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app i)).obj X₀) ∧
      Nonempty (Y ≅ (Over.pullback (c.π.app i)).obj Y₀) := by
  obtain ⟨iX, X₀, hX₀, ⟨eX⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  obtain ⟨iY, Y₀, hY₀, ⟨eY⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc Y hY
  obtain ⟨i, fX, fY, _⟩ := IsCofilteredOrEmpty.cone_objs iX iY
  refine ⟨i, (Over.pullback (D.map fX)).obj X₀,
    (Over.pullback (D.map fY)).obj Y₀,
    finitePresentation_overPullback _ _ hX₀,
    finitePresentation_overPullback _ _ hY₀, ?_, ?_⟩
  · exact ⟨eX ≪≫ overPullbackCongr (c.w fX).symm X₀ ≪≫
      (Over.pullbackComp (c.π.app i) (D.map fX)).app X₀⟩
  · exact ⟨eY ≪≫ overPullbackCongr (c.w fY).symm Y₀ ≪≫
      (Over.pullbackComp (c.π.app i) (D.map fY)).app Y₀⟩

/-- A scheme over `B` is the base change along an isomorphism `B ≅ B'` of its pushforward to
`B'`. -/
private noncomputable def overIsoPullbackMap {B B' : Scheme.{u}}
    (e : B ≅ B') (X : Over B) :
    X ≅ (Over.pullback e.hom).obj ((Over.map e.hom).obj X) :=
  asIso ((Over.mapPullbackAdj e.hom).unit.app X)

/-- Two schemes of finite presentation over a stage of a cofiltered system whose base changes to
the limit are isomorphic over it become isomorphic over some later stage. -/
private theorem exists_iso_after_baseChange
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : J) (X Y : Over (D.obj i))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (h : Nonempty ((Over.pullback (c.π.app i)).obj X ≅
      (Over.pullback (c.π.app i)).obj Y)) :
    ∃ (j : J) (f : j ⟶ i), Nonempty ((Over.pullback (D.map f)).obj X ≅
      (Over.pullback (D.map f)).obj Y) := by
  obtain ⟨h⟩ := h
  obtain ⟨j, f, g, α, β, _, _, hg⟩ :=
    AlgebraicGeometry.exists_morphism_after_baseChange D c hc i X Y hX hY h.hom
  have hg' : (Over.pullback (c.π.app j)).map g = α.hom ≫ h.hom ≫ β.inv := by
    apply (cancel_mono β.hom).mp
    simpa using hg.symm
  have : IsIso ((Over.pullback (c.π.app j)).map g) := by
    rw [hg']
    infer_instance
  have key (Z : Over (D.obj i)) (hZ : AlgebraicGeometry.FinitePresentation Z.hom) :
      LocallyOfFinitePresentation ((Over.pullback (D.map f)).obj Z).hom ∧
      QuasiCompact ((Over.pullback (D.map f)).obj Z).hom ∧
      QuasiSeparated ((Over.pullback (D.map f)).obj Z).hom ∧
      CompactSpace ((Over.pullback (D.map f)).obj Z).left ∧
      QuasiSeparatedSpace ((Over.pullback (D.map f)).obj Z).left := by
    obtain ⟨h₁, h₂, h₃⟩ := finitePresentation_overPullback (D.map f) Z hZ
    exact ⟨h₁, h₂, h₃,
      QuasiCompact.compactSpace_of_compactSpace ((Over.pullback (D.map f)).obj Z).hom,
      quasiSeparatedSpace_of_quasiSeparated ((Over.pullback (D.map f)).obj Z).hom⟩
  obtain ⟨_, _, _, _, _⟩ := key X hX
  obtain ⟨_, _, _, _, _⟩ := key Y hY
  have : LocallyOfFinitePresentation
      (g.left ≫ ((Over.pullback (D.map f)).obj Y).hom) := by
    rw [g.w]
    infer_instance
  have : LocallyOfFinitePresentation g.left :=
    AlgebraicGeometry.locallyOfFinitePresentation_of_comp g.left
      ((Over.pullback (D.map f)).obj Y).hom
  have : IsIso ((Over.pullback (c.π.app j)).map g).left :=
    inferInstanceAs (IsIso ((Over.forget c.pt).map ((Over.pullback (c.π.app j)).map g)))
  obtain ⟨k, e, he⟩ :=
    AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange D c hc j _ _ g
  have : IsIso ((Over.pullback (D.map e)).map g) := by
    have : IsIso ((Over.forget (D.obj k)).map ((Over.pullback (D.map e)).map g)) := he
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨k, e ≫ f, ⟨?_⟩⟩
  exact overPullbackCongr (D.map_comp e f) X ≪≫
    (Over.pullbackComp (D.map e) (D.map f)).app X ≪≫
    asIso ((Over.pullback (D.map e)).map g) ≪≫
    ((Over.pullbackComp (D.map e) (D.map f)).app Y).symm ≪≫
    overPullbackCongr (D.map_comp e f).symm Y

/-- Two base changes along a composite are isomorphic iff they are after base changing in two
steps. -/
private theorem nonempty_iso_pullback_comp_iff {P S B : Scheme.{u}} (f : P ⟶ S) (g : S ⟶ B)
    (X Y : Over B) :
    Nonempty ((Over.pullback (f ≫ g)).obj X ≅ (Over.pullback (f ≫ g)).obj Y) ↔
      Nonempty ((Over.pullback f).obj ((Over.pullback g).obj X) ≅
        (Over.pullback f).obj ((Over.pullback g).obj Y)) :=
  ⟨fun ⟨h⟩ => ⟨((Over.pullbackComp f g).app X).symm ≪≫ h ≪≫ (Over.pullbackComp f g).app Y⟩,
    fun ⟨h⟩ => ⟨(Over.pullbackComp f g).app X ≪≫ h ≪≫ ((Over.pullbackComp f g).app Y).symm⟩⟩

/-- Let `S` be of finite presentation over a stage of a cofiltered system and let `X, Y` be of
finite presentation over `S`. A morphism from the limit to `S` over the system along which `X`
and `Y` become isomorphic factors through a later stage, over which they are already
isomorphic. -/
private theorem exists_stage_fiber_iso
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : J) (S : Over (D.obj i)) (hS : AlgebraicGeometry.FinitePresentation S.hom)
    (X Y : Over S.left) (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (a : c.pt ⟶ S.left) (ha : a ≫ S.hom = c.π.app i)
    (h : Nonempty ((Over.pullback a).obj X ≅ (Over.pullback a).obj Y)) :
    ∃ (j : J) (f : j ⟶ i) (b : D.obj j ⟶ S.left),
      b ≫ S.hom = D.map f ∧ c.π.app j ≫ b = a ∧
      Nonempty ((Over.pullback b).obj X ≅ (Over.pullback b).obj Y) := by
  let D' := Over.forget i ⋙ D
  let c' := c.whisker (Over.forget i)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let t : D' ⟶ (Functor.const _).obj (D.obj i) := {
    app j := D.map j.hom
    naturality j k f := by
      change D.map f.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
      rw [← D.map_comp, f.w, Category.comp_id] }
  have : ∀ {j k} (f : j ⟶ k), IsAffineHom (D'.map f) := by
    intro j k f
    change IsAffineHom (D.map f.left)
    infer_instance
  have : ∀ j, CompactSpace (D'.obj j) := fun j => inferInstanceAs
    (CompactSpace (D.obj j.left))
  have : ∀ j, QuasiSeparatedSpace (D'.obj j) := fun j => inferInstanceAs
    (QuasiSeparatedSpace (D.obj j.left))
  have := hS.1
  obtain ⟨j, b, hb, hbS⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t S.hom c' hc' a
      (by ext j; exact (c.w j.hom).trans ha.symm)
  have h' : Nonempty ((Over.pullback (c.π.app j.left)).obj ((Over.pullback b).obj X) ≅
      (Over.pullback (c.π.app j.left)).obj ((Over.pullback b).obj Y)) := by
    subst hb
    exact (nonempty_iso_pullback_comp_iff _ _ X Y).mp h
  obtain ⟨k, f, ⟨e⟩⟩ := exists_iso_after_baseChange D c hc j.left
    ((Over.pullback b).obj X) ((Over.pullback b).obj Y)
    (finitePresentation_overPullback _ _ hX) (finitePresentation_overPullback _ _ hY) h'
  refine ⟨k, f ≫ j.hom, D.map f ≫ b, ?_, ?_, ?_⟩
  · simp only [Category.assoc, hbS, D.map_comp]
    rfl
  · rwa [← Category.assoc, c.w f]
  · exact (nonempty_iso_pullback_comp_iff _ _ X Y).mpr ⟨e⟩

/-- The two ways of base changing a scheme around a commutative square of bases agree. -/
private noncomputable def pullbackSquareIso
    {P S T B : Scheme.{u}} (p : P ⟶ S) (q : P ⟶ T)
    (a : S ⟶ B) (b : T ⟶ B) (w : p ≫ a = q ≫ b) (X : Over B) :
    (Over.pullback p).obj ((Over.pullback a).obj X) ≅
      (Over.pullback q).obj ((Over.pullback b).obj X) :=
  ((Over.pullbackComp p a).app X).symm ≪≫ overPullbackCongr w X ≪≫
    (Over.pullbackComp q b).app X

/-- An inclusion of finitely generated `ℤ`-subalgebras is a ring map of finite type. -/
private theorem finiteType_finGenSubalgebra_map {K : Type u} [CommRing K]
    {i j : FinGenSubalgebraIndex K} (f : i ⟶ j) :
    ((finGenSubalgebraDiagram K).map f).hom.FiniteType := by
  have : Algebra.FiniteType ℤ j.1 := (Subalgebra.fg_iff_finiteType j.1).mp j.2
  change (Subalgebra.inclusion (leOfHom f)).toRingHom.FiniteType
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ i.1)
  have he : (Subalgebra.inclusion (leOfHom f)).toRingHom.comp (algebraMap ℤ i.1) =
      algebraMap ℤ j.1 := RingHom.ext_int _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- Let `S` be of finite type over a field `K` and let `X, Y` be of finite type over `S`. There
is a countable set `I`, for each `i` a finite-type morphism `S i ⟶ S` and an isomorphism
`X ×_S S i ≅ Y ×_S S i` over `S i`, such that every `K`-point of `S` with isomorphic fibres
factors through some `S i ⟶ S`. -/
public theorem exists_countable_finiteType_isomorphism_families
    {K : Type u} [Field K]
    (S : Over (Spec (.of K))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (X Y : Over S.left)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    ∃ (I : Type (u + 1)) (_ : Countable I) (T : I → Over S.left)
      (_ : ∀ i, LocallyOfFiniteType (T i).hom ∧ QuasiCompact (T i).hom)
      (_ : ∀ i, (Over.pullback (T i).hom).obj X ≅ (Over.pullback (T i).hom).obj Y),
      ∀ (s : Over.mk (𝟙 (Spec (.of K))) ⟶ S),
        Nonempty ((Over.pullback s.left).obj X ≅ (Over.pullback s.left).obj Y) →
          ∃ (i : I) (t : Spec (.of K) ⟶ (T i).left),
            t ≫ (T i).hom = s.left := by
  classical
  let J := FinGenSubalgebraIndex K
  have : Nonempty J := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsFiltered J := finGenSubalgebraIndex_isFiltered K
  have : IsCofiltered Jᵒᵖ := inferInstance
  let R := finGenSubalgebraDiagram K
  let D : Jᵒᵖ ⥤ Scheme.{u} := R.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (finGenSubalgebraCocone K).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (finGenSubalgebraCocone_isColimit K).op
  have : ∀ {i j : Jᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := by
    intro i j e
    dsimp [D, R, finGenSubalgebraDiagram]
    infer_instance
  have : ∀ i : Jᵒᵖ, IsAffine (D.obj i) := by
    intro i
    dsimp [D, R, finGenSubalgebraDiagram]
    infer_instance
  have : ∀ i : Jᵒᵖ, CompactSpace (D.obj i) := by
    intro i
    change CompactSpace (Spec (CommRingCat.of (↑i.unop.1)))
    infer_instance
  have : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  have hSfp := AlgebraicGeometry.finitePresentation_of_finiteType S.hom
  obtain ⟨iS, S₀, hS₀, eS⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc S hSfp
  obtain ⟨eS⟩ := eS
  let F := Over.pullback S₀.hom ⋙ Over.forget S₀.left
  let D' := Over.post (X := iS) D ⋙ F
  let c' := F.mapCone (c.overPost iS)
  have hc' : IsLimit c' := isLimitOfPreserves F (hc.overPost iS)
  let e : S.left ≅ c'.pt :=
    (Over.forget _).mapIso eS ≪≫ pullbackSymmetry S₀.hom (c.π.app iS)
  have hS₀ft : LocallyOfFiniteType S₀.hom := by
    have := hS₀.1
    infer_instance
  have : QuasiCompact S₀.hom := hS₀.2.1
  have : QuasiSeparated S₀.hom := hS₀.2.2
  have : ∀ i, CompactSpace (D'.obj i) := fun i => by
    change CompactSpace (pullback (D.map i.hom) S₀.hom : Scheme)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i => by
    change QuasiSeparatedSpace (pullback (D.map i.hom) S₀.hom : Scheme)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom (D'.map f) := by
    intro i j f
    change IsAffineHom ((Over.pullback S₀.hom).map ((Over.post D).map f)).left
    exact MorphismProperty.overPullbackMap (P := @IsAffineHom) _ _
      (inferInstanceAs (IsAffineHom (D.map f.left)))
  have : IsLocallyNoetherian S.left := LocallyOfFiniteType.isLocallyNoetherian S.hom
  have hmap (Z : Over S.left) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] :
      AlgebraicGeometry.FinitePresentation ((Over.map e.hom).obj Z).hom := by
    have := (AlgebraicGeometry.finitePresentation_of_finiteType Z.hom).1
    have := (AlgebraicGeometry.finitePresentation_of_finiteType Z.hom).2.2
    change AlgebraicGeometry.FinitePresentation (Z.hom ≫ e.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, XoverS, YoverS, hX₂, hY₂, ⟨eX⟩, ⟨eY⟩⟩ :=
    exists_common_models D' c' hc' ((Over.map e.hom).obj X)
      ((Over.map e.hom).obj Y) (hmap X) (hmap Y)
  let a : S.left ⟶ D'.obj j := e.hom ≫ c'.π.app j
  have hmodel {Z : Over S.left} {Z₀ : Over (D'.obj j)}
      (eZ : (Over.map e.hom).obj Z ≅ (Over.pullback (c'.π.app j)).obj Z₀) :
      Z ≅ (Over.pullback a).obj Z₀ :=
    overIsoPullbackMap e Z ≪≫ (Over.pullback e.hom).mapIso eZ ≪≫
      ((Over.pullbackComp e.hom (c'.π.app j)).app Z₀).symm
  let ex := hmodel eX
  let ey := hmodel eY
  let A := j.left.unop.1
  have : Countable (↑A : Type u) := countable_fg_subalgebra A j.left.unop.2
  have : Algebra.FiniteType ℤ (↑A) :=
    (Subalgebra.fg_iff_finiteType A).mp j.left.unop.2
  have : IsNoetherianRing (↑A) := Algebra.FiniteType.isNoetherianRing ℤ (↑A)
  let Sbase : Over (Spec (.of (↑A))) :=
    Over.mk (pullback.fst (D.map j.hom) S₀.hom)
  have hS₂X : AlgebraicGeometry.FinitePresentation Sbase.hom := by
    have : LocallyOfFinitePresentation S₀.hom := hS₀.1
    change AlgebraicGeometry.FinitePresentation (pullback.fst (D.map j.hom) S₀.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have ha : a ≫ Sbase.hom = S.hom ≫ c.π.app j.left := by
    have hπ : c'.π.app j ≫ Sbase.hom =
        pullback.fst (c.π.app iS) S₀.hom ≫ c.π.app j.left := by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      exact pullback.lift_fst _ _ _
    have he : e.hom ≫ pullback.fst (c.π.app iS) S₀.hom = S.hom := by
      change (eS.hom.left ≫ (pullbackSymmetry _ _).hom) ≫ _ = _
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
      exact eS.hom.w
    have h₁ : a ≫ Sbase.hom = e.hom ≫ c'.π.app j ≫ Sbase.hom := Category.assoc _ _ _
    have h₂ : e.hom ≫ c'.π.app j ≫ Sbase.hom
        = e.hom ≫ pullback.fst (c.π.app iS) S₀.hom ≫ c.π.app j.left :=
      congrArg (fun t => e.hom ≫ t) hπ
    have h₃ : e.hom ≫ pullback.fst (c.π.app iS) S₀.hom ≫ c.π.app j.left
        = (e.hom ≫ pullback.fst (c.π.app iS) S₀.hom) ≫ c.π.app j.left :=
      (Category.assoc _ _ _).symm
    have h₄ : (e.hom ≫ pullback.fst (c.π.app iS) S₀.hom) ≫ c.π.app j.left
        = S.hom ≫ c.π.app j.left :=
      congrArg (fun t => t ≫ c.π.app j.left) he
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  let P : Over (Spec (.of (↑A))) → Prop := fun Z =>
    LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom
  let C := ObjectProperty.FullSubcategory P
  let Q := Quotient (isIsomorphicSetoid C)
  have hQ : Countable Q :=
    AlgebraicGeometry.countable_isomorphismClasses_of_finiteType (↑A)
  let rep (q : Q) : C := Quotient.out q
  let M := Σ q : Q, (rep q).obj ⟶ Sbase
  have hM : Countable M := by
    have : ∀ q : Q, Countable ((rep q).obj ⟶ Sbase) := fun q => by
      have : LocallyOfFiniteType (rep q).obj.hom := (rep q).property.1
      have : QuasiCompact (rep q).obj.hom := (rep q).property.2
      have : LocallyOfFinitePresentation Sbase.hom := hS₂X.1
      have : LocallyOfFiniteType Sbase.hom := inferInstance
      have : QuasiCompact Sbase.hom := hS₂X.2.1
      exact AlgebraicGeometry.countable_hom_of_finiteType
        (rep q).obj Sbase
    infer_instance
  let Good (m : M) : Prop :=
    Nonempty ((Over.pullback m.2.left).obj XoverS ≅
      (Over.pullback m.2.left).obj YoverS)
  let I := {m : M // Good m}
  let Tbase (i : I) : Over Sbase.left := Over.mk i.1.2.left
  have hTbase (i : I) :
      LocallyOfFiniteType (Tbase i).hom ∧ QuasiCompact (Tbase i).hom := by
    let q := i.1.1
    let f := i.1.2
    have : LocallyOfFiniteType (rep q).obj.hom := (rep q).property.1
    have : QuasiCompact (rep q).obj.hom := (rep q).property.2
    have hcomp : LocallyOfFiniteType (f.left ≫ Sbase.hom) := by
      rw [f.w]
      exact (rep q).property.1
    have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Sbase.hom
    have : IsLocallyNoetherian (rep q).obj.left :=
      LocallyOfFiniteType.isLocallyNoetherian (rep q).obj.hom
    have : CompactSpace (rep q).obj.left :=
      QuasiCompact.compactSpace_of_compactSpace (rep q).obj.hom
    have : IsNoetherian (rep q).obj.left := {}
    have : QuasiCompact f.left := quasiCompact_of_noetherianSpace_source f.left
    exact ⟨by change LocallyOfFiniteType f.left; infer_instance,
      by change QuasiCompact f.left; infer_instance⟩
  let T (i : I) : Over S.left := (Over.pullback a).obj (Tbase i)
  have hT (i : I) : LocallyOfFiniteType (T i).hom ∧ QuasiCompact (T i).hom := by
    change LocallyOfFiniteType (pullback.snd (Tbase i).hom a) ∧
      QuasiCompact (pullback.snd (Tbase i).hom a)
    exact ⟨locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (Tbase i).hom a) (hTbase i).1,
      quasiCompact_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (Tbase i).hom a) (hTbase i).2⟩
  let H (i : I) : (Over.pullback (T i).hom).obj X ≅
      (Over.pullback (T i).hom).obj Y :=
    (Over.pullback (T i).hom).mapIso ex ≪≫
    pullbackSquareIso (T i).hom (pullback.fst (Tbase i).hom a) a (Tbase i).hom
      pullback.condition.symm XoverS ≪≫
    (Over.pullback (pullback.fst (Tbase i).hom a)).mapIso (Classical.choice i.2) ≪≫
    (pullbackSquareIso (T i).hom (pullback.fst (Tbase i).hom a) a (Tbase i).hom
      pullback.condition.symm YoverS).symm ≪≫
    (Over.pullback (T i).hom).mapIso ey.symm
  refine ⟨I, inferInstance, T, hT, H, ?_⟩
  intro s hs
  have hs' : Nonempty ((Over.pullback (s.left ≫ a)).obj XoverS ≅
      (Over.pullback (s.left ≫ a)).obj YoverS) := by
    obtain ⟨h⟩ := hs
    exact (nonempty_iso_pullback_comp_iff _ _ XoverS YoverS).mpr
      ⟨(Over.pullback s.left).mapIso ex.symm ≪≫ h ≪≫ (Over.pullback s.left).mapIso ey⟩
  obtain ⟨k, f, b, hbS, hb, ⟨eh⟩⟩ := exists_stage_fiber_iso D c hc j.left
    Sbase hS₂X XoverS YoverS hX₂ hY₂ (s.left ≫ a)
    (by
      have k₁ : (s.left ≫ a) ≫ Sbase.hom = s.left ≫ a ≫ Sbase.hom :=
        Category.assoc _ _ _
      have k₂ : s.left ≫ a ≫ Sbase.hom = s.left ≫ S.hom ≫ c.π.app j.left :=
        congrArg (fun t => s.left ≫ t) ha
      have k₃ : s.left ≫ S.hom ≫ c.π.app j.left
          = (s.left ≫ S.hom) ≫ c.π.app j.left := (Category.assoc _ _ _).symm
      have k₄ : (s.left ≫ S.hom) ≫ c.π.app j.left = c.π.app j.left :=
        (congrArg (fun t => t ≫ c.π.app j.left) (Over.w s)).trans (Category.id_comp _)
      exact k₁.trans (k₂.trans (k₃.trans k₄))) hs'
  have hkft : LocallyOfFiniteType (D.map f) := by
    change LocallyOfFiniteType (Spec.map ((finGenSubalgebraDiagram K).map f.unop))
    exact HasRingHomProperty.Spec_iff.mpr (finiteType_finGenSubalgebra_map f.unop)
  have hkqc : QuasiCompact (D.map f) := inferInstance
  let Z : C := ⟨Over.mk (D.map f), hkft, hkqc⟩
  let q : Q := Quotient.mk _ Z
  obtain ⟨eq₀⟩ : Nonempty (rep q ≅ Z) := Quotient.exact (Quotient.out_eq q)
  let eq : (rep q).obj ≅ Z.obj := (ObjectProperty.ι P).mapIso eq₀
  let m : M := ⟨q, eq.hom ≫ Over.homMk b hbS⟩
  have hm : Good m :=
    (nonempty_iso_pullback_comp_iff _ _ XoverS YoverS).mpr ⟨(Over.pullback eq.hom.left).mapIso eh⟩
  let i : I := ⟨m, hm⟩
  have ht : (c.π.app k ≫ eq.inv.left) ≫ (Tbase i).hom = s.left ≫ a := by
    change (c.π.app k ≫ eq.inv.left) ≫ (eq.hom.left ≫ b) = _
    have heq : eq.inv.left ≫ eq.hom.left = 𝟙 _ :=
      congrArg Over.Hom.left eq.inv_hom_id
    have m₁ : (c.π.app k ≫ eq.inv.left) ≫ (eq.hom.left ≫ b)
        = c.π.app k ≫ eq.inv.left ≫ eq.hom.left ≫ b := Category.assoc _ _ _
    have m₂ : eq.inv.left ≫ eq.hom.left ≫ b = b :=
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ b) heq)).trans (Category.id_comp b)
    exact (m₁.trans (congrArg (fun t => c.π.app k ≫ t) m₂)).trans hb
  exact ⟨i, pullback.lift (c.π.app k ≫ eq.inv.left) s.left ht, pullback.lift_snd _ _ _⟩

/-- For `S` of finite type over an algebraically closed field `K` and `X, Y` of finite type over
`S`, there is a countable set `I`, for each `i` a finite-type morphism `S i ⟶ S` and an
isomorphism `X ×_S S i ≅ Y ×_S S i` over `S i`, such that every closed point of `S` valued in `K`
whose two fibres are isomorphic over `K` lies in the image of some `S i ⟶ S`. -/
@[stacks 0G0X]
public theorem exists_countable_finiteType_isomorphism_families_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (S : Over (Spec (.of K))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (X Y : Over S.left)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    ∃ (I : Type (u + 1)) (_ : Countable I) (T : I → Over S.left)
      (_ : ∀ i, LocallyOfFiniteType (T i).hom ∧ QuasiCompact (T i).hom)
      (_ : ∀ i, (Over.pullback (T i).hom).obj X ≅ (Over.pullback (T i).hom).obj Y),
      ∀ (s : Over.mk (𝟙 (Spec (.of K))) ⟶ S),
        Nonempty ((Over.pullback s.left).obj X ≅ (Over.pullback s.left).obj Y) →
          ∃ (i : I) (t : Spec (.of K) ⟶ (T i).left),
            t ≫ (T i).hom = s.left :=
  exists_countable_finiteType_isomorphism_families S X Y

end AlgebraicGeometry

end
