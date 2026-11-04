module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaReduction
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chow's lemma over a quasi-compact quasi-separated base

Let `S` be quasi-compact and quasi-separated and let `f : X ⟶ S` be separated and of finite
type. **Chow's lemma** ([Stacks, Tag 0202]) produces a proper surjective `π : X' ⟶ X` with `X'`
immersed in a projective space over `S`, compatibly with the maps to `S`. When `X` has only
finitely many irreducible components, the **variant** [Stacks, Tag 0203] produces in addition a
dense open `U ⊆ X` over which `π` is an isomorphism.

Both are proved here from Chow's lemma over a *Noetherian* base ([Stacks, Tag 0200], formalized as
`AlgebraicGeometry.hasDenseChowModification`) by absolute Noetherian approximation.

## The two proofs

Tag 0202 needs nothing beyond base change. Reduction 1 replaces `X` by a scheme `Y` that is
separated and of finite presentation over `S` and into which `X` closed-immerses
([Stacks, Tag 01ZJ]); reduction 2 writes `S = lim Sᵢ` as a limit of Noetherian schemes with
affine transitions ([Stacks, Tag 01ZA]), descends `Y` to a separated `Yᵢ` of finite presentation
over a stage ([Stacks, Tag 01ZM] part (1) and [Stacks, Tag 01ZQ]), applies Tag 0200 there and
base changes the modification back. Both reductions are already available: the second is
`AlgebraicGeometry.hasChowModification_of_finitePresentation`, which carries Tag 0200 as the
hypothesis `AlgebraicGeometry.ChowOverNoetherianBase`, and that hypothesis is discharged here by
`AlgebraicGeometry.chowOverNoetherianBase`.

Tag 0203 cannot be had the same way, because **a dense open does not survive base change**: the
dense open of `Xᵢ` that Tag 0200 returns pulls back to an open of `X = S ×_{Sᵢ} Xᵢ` which need
not be dense. The Stacks proof therefore keeps the whole limit in play. Having descended `Y` to
`Y₁` over a stage `i₁`, it forms the inverse system `Yⱼ = Sⱼ ×_{S_{i₁}} Y₁` for `j ≥ i₁`, whose
limit is `Y`; the finitely many generic points of `X` have pairwise non-specializing images at
some stage `j` of that system, because non-specialization in a cofiltered limit of schemes with
affine transitions is witnessed at a stage. Tag 0200 is then applied not to `Yⱼ` but to the
**scheme-theoretic image** `Z` of `X ⟶ Yⱼ`: the generic points of `X` map to generic points of
`Z` ([Stacks, Tag 01RL] and the dominance of `X ⟶ Z`), so the dense open of `Z` contains all of
them, and its preimage in `X` contains every generic point of `X` and is therefore dense.

## Main results

* `AlgebraicGeometry.chowOverNoetherianBase`: Chow's lemma over a Noetherian base in the form
  the reductions of Tag 0202 consume, discharged from Tag 0200.
* `AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`:
  **[Stacks, Tag 0202]**.
* `AlgebraicGeometry.hasDenseChowModification_of_finite_irreducibleComponents`:
  **[Stacks, Tag 0203]**.

## Implementation notes

`AlgebraicGeometry.hasDenseChowModification_of_baseChange` is the transport step, and it is
stated with the hypothesis that `X ⟶ Z ×_T S` is an immersion rather than that `X ⟶ Z` is one:
that is what the closed immersion of Tag 01ZJ supplies after `Z` is replaced by a stage model,
and it is exactly what makes the pulled-back modification immerse into `ℙⁿ_S`. The
identification `ℙⁿ_T ×_T S ≅ ℙⁿ_S` is `AlgebraicGeometry.ProjectiveSpace.baseChangeIso`.

The inverse system `Yⱼ` and its limit cone are those of
`AlgebraicGeometry.pullbackDiagram` and `AlgebraicGeometry.isLimitPullbackCone` (Tag 01YZ),
indexed by `CategoryTheory.Over i₁`. They are nevertheless *respelled* here as a structure
literal definitionally equal to them, inheriting the functor and cone laws from the library
versions. The reason is transparency: `(pullbackDiagram D i₁ Y₁.hom).obj j` reaches
`Limits.pullback (D.map j.hom) Y₁.hom` only by unfolding semireducible definitions, so a
composite such as `a ≫ cE.π.app j` is not type-correct at reducible transparency and every
`rw` touching it fails. Written as a structure literal the same reductions are projections,
which `rw` can see.

For the same reason the pullback calculations below are done with explicit
`CategoryTheory.Limits.pullback.lift_fst` and `pullback.lift_snd` terms rather than `simp`:
those lemmas do not fire here, because the `simp`-normal form of a pullback would require
unfolding `CategoryTheory.Limits.getLimitCone`, whose definition this module does not expose.

## References

* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0203](https://stacks.math.columbia.edu/tag/0203)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [EGA II, Theorem 5.6.1(b)]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points -/

/-- A point specializing to a generic point equals it. -/
theorem eq_of_specializes_genericPoints {T : Type*} [TopologicalSpace T] [T0Space T] {x y : T}
    (hy : y ∈ genericPoints T) (h : x ⤳ y) : x = y :=
  (h.antisymm (specializes_iff_closure_subset.mpr
    (hy.2 isIrreducible_singleton.closure h.closure_subset))).eq

/-- Every point of a space specializes from a generic point of an irreducible component. -/
theorem exists_genericPoints_specializes {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (x : T) : ∃ η : genericPoints T, η.1 ⤳ x :=
  ⟨genericPoints.ofComponent ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩,
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent⟩

/-- **A dense open of a Noetherian space contains every generic point.** An irreducible
component has a nonempty open subset, which the dense open meets; a generic point of that
component lies in every open meeting the component. -/
theorem genericPoints_mem_of_dense {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (V : Opens T) (hV : Dense (V : Set T)) (η : genericPoints T) : η.1 ∈ V := by
  obtain ⟨W, hW, hne, hsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ η.2
  obtain ⟨x, hxV, hxW⟩ := hV.exists_mem_open hW hne
  exact ((genericPoints.isGenericPoint η).mem_open_set_iff V.isOpen).2 ⟨x, hsub hxW, hxV⟩

/-- **A dominant quasi-compact morphism that does not collapse generic points maps them to
generic points.** If no generic point of `X` has an image specializing to the image of a
different one, then the image of a generic point of `X` is a generic point of `Y`.

Dominance enters through [Stacks, Tag 01RL]: every generic point of `Y` is hit. -/
theorem mapsTo_genericPoints_of_forall_not_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsDominant f]
    (hf : ∀ a b : genericPoints X, a ≠ b → ¬f a.1 ⤳ f b.1) :
    Set.MapsTo f (genericPoints X) (genericPoints Y) := by
  intro η hη
  obtain ⟨y, hyη⟩ := exists_genericPoints_specializes (f η)
  obtain ⟨x, hx⟩ :=
    (isDominant_iff_genericPoints_subset_range f).1 inferInstance y.2
  obtain ⟨ξ, hξ⟩ := exists_genericPoints_specializes x
  have hξy : f ξ.1 ⤳ y.1 := by simpa only [hx] using hξ.map f.continuous
  have heq : ξ = ⟨η, hη⟩ := by
    by_contra hn
    exact hf ξ ⟨η, hη⟩ hn (hξy.trans hyη)
  have hηy : f η ⤳ y.1 := by simpa only [heq, hx] using hξ.map f.continuous
  simpa only [eq_of_specializes_genericPoints y.2 hηy] using y.2

/-! ### Non-specialization at a stage -/

/-- **Non-specialization in a cofiltered limit is witnessed at a stage.** In a limit of schemes
with affine transition morphisms the preimages of affine opens form a basis, so an open
separating two points is refined by the preimage of an open at some stage. -/
theorem exists_not_specializes_π_app {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) (cE : Cone E) (hcE : IsLimit cE)
    [∀ {j k : J} (e : j ⟶ k), IsAffineHom (E.map e)] {x y : cE.pt} (hxy : ¬x ⤳ y) :
    ∃ j, ¬cE.π.app j x ⤳ cE.π.app j y := by
  obtain ⟨U, hU, hy, hx⟩ := not_specializes_iff_exists_open.mp hxy
  obtain ⟨V, ⟨j, W, hW, rfl⟩, hyW, hWU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen' E cE hcE))
      (show y ∈ (⟨U, hU⟩ : cE.pt.Opens) from hy)
  exact ⟨j, fun h => hx (hWU (h.mem_open W.isOpen hyW))⟩

/-! ### Transporting a dense modification along a base change -/

/-- The restriction of a pullback projection to the preimage of an open over which the other
projection's base is an isomorphism is an isomorphism. -/
theorem isIso_restrict_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (V : Z.Opens)
    [IsIso (g ∣_ V)] : IsIso (pullback.fst f g ∣_ (f ⁻¹ᵁ V)) := by
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g).flip
    (US := V) (UT := f ⁻¹ᵁ V) (UX := g ⁻¹ᵁ V) le_rfl le_rfl
    (UY := pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ V) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
      exact (inf_idem _).symm)
  have : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using H.isIso_snd_of_isIso

/-- A map `Q ×_C D ⟶ B ×_C D` over a factorization `t = u ≫ v` through `B` is a base change of
`u` if it is compatible with both projections. -/
private theorem isPullback_of_comp_projections {A B C D : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C)
    (w : D ⟶ C) (t : A ⟶ C) (ht : u ≫ v = t) (m : pullback t w ⟶ pullback v w)
    (hf : m ≫ pullback.fst v w = pullback.fst t w ≫ u)
    (hs : m ≫ pullback.snd v w = pullback.snd t w) :
    IsPullback m (pullback.fst t w) (pullback.fst v w) u := by
  subst ht
  refine IsPullback.of_right ?_ hf (IsPullback.of_hasPullback v w).flip
  rw [hs]
  exact (IsPullback.of_hasPullback _ w).flip

/-- **An immersion into a base change stays an immersion after a further base change of the
target.** If `X ⟶ Z ×_T S` is an immersion then so is `Y ×_Z X ⟶ (Y ×_Z Z) ×_T S`, for any
`r : Y ⟶ Z`. -/
theorem isImmersion_pullbackLift_baseChange {X Y Z S T : Scheme.{u}} (f : X ⟶ S) (k : X ⟶ Z)
    (g : Z ⟶ T) (p : S ⟶ T) (w : k ≫ g = f ≫ p) [IsImmersion (pullback.lift k f w)]
    (r : Y ⟶ Z) :
    IsImmersion (pullback.lift (pullback.snd k r) (pullback.fst k r ≫ f)
      (show pullback.snd k r ≫ (r ≫ g) = (pullback.fst k r ≫ f) ≫ p by
        rw [← Category.assoc, ← pullback.condition, Category.assoc, w, Category.assoc])) := by
  let a : X ⟶ pullback g p := pullback.lift k f w
  have haf : a ≫ pullback.fst g p = k := pullback.lift_fst _ _ _
  have has : a ≫ pullback.snd g p = f := pullback.lift_snd _ _ _
  let b : pullback (r ≫ g) p ⟶ pullback g p :=
    pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  have hbf : b ≫ pullback.fst g p = pullback.fst (r ≫ g) p ≫ r := pullback.lift_fst _ _ _
  have hbs : b ≫ pullback.snd g p = pullback.snd (r ≫ g) p := pullback.lift_snd _ _ _
  have hb : IsPullback b (pullback.fst (r ≫ g) p) (pullback.fst g p) r :=
    isPullback_of_comp_projections r g p _ rfl b hbf hbs
  let j : pullback k r ⟶ pullback (r ≫ g) p :=
    pullback.lift (pullback.snd k r) (pullback.fst k r ≫ f) (by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, w, Category.assoc])
  have hjf : j ≫ pullback.fst (r ≫ g) p = pullback.snd k r := pullback.lift_fst _ _ _
  have hjs : j ≫ pullback.snd (r ≫ g) p = pullback.fst k r ≫ f := pullback.lift_snd _ _ _
  have hmid : j ≫ b = pullback.fst k r ≫ a := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hbf, haf, reassoc_of% hjf]
      exact pullback.condition.symm
    · simp only [Category.assoc, hbs, has, hjs]
  have houter : IsPullback (j ≫ pullback.fst (r ≫ g) p) (pullback.fst k r) r
      (a ≫ pullback.fst g p) := by
    rw [hjf, haf]
    exact (IsPullback.of_hasPullback k r).flip
  have hj : IsPullback j (pullback.fst k r) b a :=
    IsPullback.of_right houter hmid hb.flip
  exact MorphismProperty.of_isPullback hj.flip ‹IsImmersion (pullback.lift k f w)›

/-- **Transporting a dense Chow modification along a base change.** Suppose `k : X ⟶ Z` and
`p : S ⟶ T` sit over `g : Z ⟶ T` and `f : X ⟶ S` in such a way that the induced
`X ⟶ Z ×_T S` is an immersion, and suppose `g` has a Chow modification `π` that is an
isomorphism over a dense open `V` whose preimage in `X` is still dense. Then `f` has a dense
Chow modification: pull `π` back along `k`.

The immersion into `ℙⁿ_S` is the composite of the base-changed immersion `X ×_Z Z' ⟶ ℙⁿ_T ×_T S`
with `AlgebraicGeometry.ProjectiveSpace.baseChangeIso`. -/
theorem hasDenseChowModification_of_baseChange {X Z S T : Scheme.{u}} (f : X ⟶ S) (k : X ⟶ Z)
    (g : Z ⟶ T) (p : S ⟶ T) (w : k ≫ g = f ≫ p) [IsImmersion (pullback.lift k f w)]
    {n : ℕ} {Z' : Scheme.{u}} (π : Z' ⟶ Z) (i : Z' ⟶ ProjectiveSpace n T) (V : Z.Opens)
    (hπ : IsProper π) (hsurj : Surjective π) (himm : IsImmersion i)
    (hcomm : π ≫ g = i ≫ (ProjectiveSpace n T ↘ T)) (hiso : IsIso (π ∣_ V))
    (hV : Dense ((k ⁻¹ᵁ V : X.Opens) : Set X)) :
    HasDenseChowModification f := by
  let π' : pullback k π ⟶ X := pullback.fst _ _
  let j : pullback k π ⟶ pullback (π ≫ g) p :=
    pullback.lift (pullback.snd k π) (π' ≫ f) (by
      dsimp [π']
      rw [← Category.assoc, ← pullback.condition, Category.assoc, w, Category.assoc])
  have : IsImmersion j := isImmersion_pullbackLift_baseChange f k g p w π
  let d : Over.mk (π ≫ g) ⟶ Over.mk (ProjectiveSpace n T ↘ T) := Over.homMk i hcomm.symm
  let dS := ((Over.pullback p).map d).left
  have : IsImmersion dS := MorphismProperty.overPullbackMap p d himm
  let e := ProjectiveSpace.baseChangeIso n p
  refine ⟨n, pullback k π, π', j ≫ dS ≫ e.hom, k ⁻¹ᵁ V, inferInstance, inferInstance,
    inferInstance, ?_, hV, isIso_restrict_pullback_fst k π V⟩
  have hd : dS ≫ pullback.snd (ProjectiveSpace n T ↘ T) p = pullback.snd (π ≫ g) p :=
    Over.w ((Over.pullback p).map d)
  symm
  rw [Category.assoc, Category.assoc, ProjectiveSpace.baseChangeIso_hom_over, hd]
  exact pullback.lift_snd _ _ _

/-! ### Chow's lemma over a quasi-compact quasi-separated base -/

/-- **Chow's lemma over a Noetherian base**, [Stacks, Tag 0200], in the form in which the
reductions of [Stacks, Tag 0202] consume it. -/
theorem chowOverNoetherianBase : ChowOverNoetherianBase.{u} :=
  fun _ _ f _ _ _ _ => hasChowModification f

/-- **Chow's lemma over a quasi-compact quasi-separated base.** A separated morphism of finite
type onto a quasi-compact quasi-separated scheme admits a proper surjective modification immersed
in a projective space over the base. -/
@[stacks 0202, sga "4 XVII 7.0.6" "(i), (iii)", sga "4 XII 7.1" "Chow diagram"]
theorem hasChowModification_of_compactSpace_quasiSeparatedSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : HasChowModification f := by
  obtain ⟨Y, g, ι, hsep, hfp, hclosed, hcomm⟩ :=
    exists_isClosedImmersion_into_isSeparated_finitePresentation f
  exact hasChowModification_of_isClosedImmersion_of_finitePresentation
    chowOverNoetherianBase.{u} hfp hcomm

/-- **The transition morphisms of a base-changed inverse system are base changes.** Hence they
are affine as soon as the transition morphisms of the original system are. -/
theorem isAffineHom_pullbackDiagram_map {I : Type u} [Category.{u} I] {T : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (i : I) (fT : T ⟶ D.obj i) {j k : Over i} (g : j ⟶ k)
    (h : IsAffineHom (D.map g.left)) : IsAffineHom ((pullbackDiagram D i fT).map g) := by
  have hm : IsPullback ((pullbackDiagram D i fT).map g) (pullback.fst (D.map j.hom) fT)
      (pullback.fst (D.map k.hom) fT) (D.map g.left) :=
    isPullback_of_comp_projections (D.map g.left) (D.map k.hom) fT (D.map j.hom)
      (by rw [← D.map_comp, Over.w g]) _
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  exact MorphismProperty.of_isPullback hm.flip h

/-- **[Stacks, Tag 0203]: the variant of Chow's lemma with a dense open.** Let `S` be
quasi-compact and quasi-separated, let `f : X ⟶ S` be separated and of finite type, and suppose
`X` has only finitely many irreducible components. Then there are `n`, a scheme `X'`, a proper
surjective `π : X' ⟶ X` and an immersion `X' ⟶ ℙⁿ_S` making the triangle over `S` commute, such
that `π` is an isomorphism over a dense open subscheme of `X`.

The dense open does not survive base change, so unlike [Stacks, Tag 0202] this cannot be had by
descending `X` to a stage and pulling the modification back. Instead the whole inverse system
`Yⱼ = Sⱼ ×_{S_{i₁}} Y₁` is kept, Chow's lemma over a Noetherian base is applied to the
**scheme-theoretic image** of `X` in a stage chosen so that the finitely many generic points of
`X` have pairwise non-specializing images, and the dense open of that image then pulls back to a
dense open of `X` because it contains every generic point. -/
@[stacks 0203,
  sga "4 XVII 7.0.6" "finite irred. components",
  ega "II 5.6.1" "(b); (i),(ii)",
  sga "4 XII 7.1" "finite irred. components"]
theorem hasDenseChowModification_of_finite_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hX : (irreducibleComponents X).Finite) :
    HasDenseChowModification f := by
  classical
  -- Absolute Noetherian approximation of the base, Tag 01ZA.
  obtain ⟨I, hI, hIne, hIdir, D, cπ, haff, hft, hqcT, ⟨hc⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType S
  let _ : Preorder I := hI
  have : Nonempty I := hIne
  have : IsDirected I (· ≤ ·) := hIdir
  let c : Cone D := Cone.mk S cπ
  have hcL : IsLimit c := hc
  have haffD : ∀ {i j : Iᵒᵈ} (e : i ⟶ j), IsAffineHom (D.map e) := fun e => haff e
  have : ∀ {i j : Iᵒᵈ} (e : i ⟶ j), IsAffineHom (D.map e) := haffD
  have hnoeth : ∀ i : Iᵒᵈ, IsNoetherian (D.obj i) := fun i =>
    isNoetherian_of_locallyOfFiniteType_terminalFrom _ (hft i) (hqcT i)
  have : ∀ i : Iᵒᵈ, IsNoetherian (D.obj i) := hnoeth
  -- Tag 01ZJ: embed `X` in a scheme separated and of finite presentation over `S`.
  obtain ⟨Y, g, ι, hsepg, hfpg, hclosed, hcommg⟩ :=
    exists_isClosedImmersion_into_isSeparated_finitePresentation f
  have : IsSeparated (Over.mk g).hom := hsepg
  -- Descend it to a separated model of finite presentation over a Noetherian stage.
  obtain ⟨i₁, Y₁, hfp₁, hsep₁, ⟨e₁⟩⟩ :=
    exists_isSeparated_finitePresentation_model_of_isLimit D c hcL (Over.mk g) hfpg
  have : LocallyOfFinitePresentation Y₁.hom := hfp₁.1
  have : QuasiCompact Y₁.hom := hfp₁.2.1
  have : LocallyOfFiniteType Y₁.hom := inferInstance
  -- The inverse system `Yⱼ = Sⱼ ×_{S_{i₁}} Y₁` for `j ≥ i₁`, with limit `Y`, Tag 01YZ.
  -- Spelled out as a structure literal, so that `E.obj` and `cE.pt` reduce by projection; the
  -- functor and cone laws are inherited from `AlgebraicGeometry.pullbackDiagram`, to which this
  -- is definitionally equal.
  let E : Over i₁ ⥤ Scheme.{u} :=
    { obj := fun jj => pullback (D.map jj.hom) Y₁.hom
      map := fun {jj kk} e =>
        pullback.lift (pullback.fst (D.map jj.hom) Y₁.hom ≫ D.map e.left)
          (pullback.snd (D.map jj.hom) Y₁.hom) (by
            rw [Category.assoc, ← D.map_comp, Over.w e]
            exact pullback.condition)
      map_id := fun jj => (pullbackDiagram D i₁ Y₁.hom).map_id jj
      map_comp := fun e e' => (pullbackDiagram D i₁ Y₁.hom).map_comp e e' }
  let cE : Cone E := Cone.mk (pullback (c.π.app i₁) Y₁.hom) (pullbackCone D c i₁ Y₁.hom).π
  have hcE : IsLimit cE := isLimitPullbackCone D c hcL i₁ Y₁.hom
  have : ∀ {j k : Over i₁} (e : j ⟶ k), IsAffineHom (E.map e) := fun e =>
    isAffineHom_pullbackDiagram_map D i₁ Y₁.hom e (haffD _)
  -- `X` closed-immerses into the limit vertex `S ×_{S_{i₁}} Y₁`.
  let eY : Y ≅ pullback (c.π.app i₁) Y₁.hom :=
    ((Over.forget S).mapIso e₁).trans (pullbackSymmetry Y₁.hom (c.π.app i₁))
  let a : X ⟶ pullback (c.π.app i₁) Y₁.hom := ι ≫ eY.hom
  have : IsClosedImmersion a := inferInstance
  have ha : a ≫ pullback.fst (c.π.app i₁) Y₁.hom = f := by
    have h1 : eY.hom ≫ pullback.fst (c.π.app i₁) Y₁.hom = g :=
      calc eY.hom ≫ pullback.fst (c.π.app i₁) Y₁.hom
            = e₁.hom.left ≫ (pullbackSymmetry Y₁.hom (c.π.app i₁)).hom ≫
                pullback.fst (c.π.app i₁) Y₁.hom := Category.assoc _ _ _
        _ = e₁.hom.left ≫ pullback.snd Y₁.hom (c.π.app i₁) := by
          rw [pullbackSymmetry_hom_comp_fst]
        _ = g := Over.w e₁.hom
    calc a ≫ pullback.fst (c.π.app i₁) Y₁.hom
          = ι ≫ eY.hom ≫ pullback.fst (c.π.app i₁) Y₁.hom := Category.assoc _ _ _
      _ = ι ≫ g := by rw [h1]
      _ = f := hcommg
  -- Choose a stage at which the images of the generic points pairwise do not specialize.
  have : Finite (genericPoints X) := (genericPoints.finite hX).to_subtype
  have hex (ab : {q : genericPoints X × genericPoints X // q.1 ≠ q.2}) :
      ∃ j : Over i₁, ¬cE.π.app j (a ab.1.1.1) ⤳ cE.π.app j (a ab.1.2.1) :=
    exists_not_specializes_π_app E cE hcE (fun hs => ab.2 (Subtype.ext
      (eq_of_specializes_genericPoints ab.1.2.2
        (a.isClosedEmbedding.isInducing.specializes_iff.mp hs))))
  choose stage hstage using hex
  have hsfin : (Set.range stage).Finite := Set.finite_range stage
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists hsfin.toFinset
  let hjX : X ⟶ pullback (D.map j.hom) Y₁.hom := a ≫ cE.π.app j
  have hdistinct (x y : genericPoints X) (hne : x ≠ y) : ¬hjX x.1 ⤳ hjX y.1 := by
    intro hs
    obtain ⟨e⟩ := hj (hsfin.mem_toFinset.mpr ⟨⟨(x, y), hne⟩, rfl⟩)
    have he (z : X) : E.map e (hjX z) = cE.π.app (stage ⟨(x, y), hne⟩) (a z) :=
      congrArg (fun t : X ⟶ E.obj (stage ⟨(x, y), hne⟩) => t z)
        (show (a ≫ cE.π.app j) ≫ E.map e = a ≫ cE.π.app (stage ⟨(x, y), hne⟩) by
          rw [Category.assoc, cE.w e])
    exact hstage ⟨(x, y), hne⟩ (by simpa only [he] using hs.map (E.map e).continuous)
  -- The stage morphism is affine, so `hjX` is quasi-compact and has a scheme-theoretic image.
  have : IsAffineHom (cE.π.app j) := isAffineHom_π_app' E cE hcE j
  have : QuasiCompact hjX := inferInstance
  have hπfst : cE.π.app j ≫ pullback.fst (D.map j.hom) Y₁.hom
      = pullback.fst (c.π.app i₁) Y₁.hom ≫ c.π.app j.left := pullback.lift_fst _ _ _
  have hπsnd : cE.π.app j ≫ pullback.snd (D.map j.hom) Y₁.hom
      = pullback.snd (c.π.app i₁) Y₁.hom := pullback.lift_snd _ _ _
  have hcart : IsPullback (cE.π.app j) (pullback.fst (c.π.app i₁) Y₁.hom)
      (pullback.fst (D.map j.hom) Y₁.hom) (c.π.app j.left) :=
    isPullback_of_comp_projections _ _ _ _ (c.w j.hom) _ hπfst hπsnd
  have hwE : hjX ≫ pullback.fst (D.map j.hom) Y₁.hom = f ≫ c.π.app j.left := by
    rw [Category.assoc, hπfst, ← Category.assoc, ha]
  have himmE : IsImmersion (pullback.lift hjX f hwE) := by
    have he : pullback.lift hjX f hwE = a ≫ hcart.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, hcart.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, hcart.isoPullback_hom_snd, ha]
    rw [he]
    infer_instance
  -- Chow's lemma over the Noetherian stage, applied to the scheme-theoretic image of `hjX`.
  have : IsNoetherian (D.obj j.left) := hnoeth _
  have : AlgebraicGeometry.IsLocallyNoetherian
      (Limits.pullback (D.map j.hom) Y₁.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (D.map j.hom) Y₁.hom)
  have : CompactSpace (Limits.pullback (D.map j.hom) Y₁.hom).carrier :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) Y₁.hom)
  let gZ : hjX.image ⟶ D.obj j.left := hjX.imageι ≫ pullback.fst (D.map j.hom) Y₁.hom
  have : AlgebraicGeometry.IsLocallyNoetherian hjX.image :=
    LocallyOfFiniteType.isLocallyNoetherian hjX.imageι
  have : CompactSpace hjX.image.carrier :=
    QuasiCompact.compactSpace_of_compactSpace hjX.imageι
  have : AlgebraicGeometry.IsNoetherian hjX.image := {}
  obtain ⟨n, Z', πZ, iP, V, hπ, hsurj, himm, hcm, hVdense, hViso⟩ :=
    hasDenseChowModification gZ
  -- The generic points of `X` land in the generic points of the image, so `V` pulls back dense.
  have hkgen : Set.MapsTo hjX.toImage (genericPoints X) (genericPoints hjX.image) := by
    refine mapsTo_genericPoints_of_forall_not_specializes _ (fun x y hne hs => ?_)
    have hv (z : X) : hjX.imageι (hjX.toImage z) = hjX z :=
      congrArg (fun t : X ⟶ pullback (D.map j.hom) Y₁.hom => t z) hjX.toImage_imageι
    exact hdistinct x y hne (by simpa only [hv] using hs.map hjX.imageι.continuous)
  have hdense : Dense ((hjX.toImage ⁻¹ᵁ V : X.Opens) : Set X) :=
    (dense_iff_closure_eq.mpr genericPoints.closure).mono fun x hx =>
      genericPoints_mem_of_dense V hVdense ⟨hjX.toImage x, hkgen hx⟩
  -- Transport the modification to `S`.
  have hw : hjX.toImage ≫ gZ = f ≫ c.π.app j.left := by
    rw [← hwE]
    exact (Category.assoc _ _ _).symm.trans (by rw [hjX.toImage_imageι])
  have himmk : IsImmersion (pullback.lift hjX.toImage f hw) := by
    have wm : (pullback.fst gZ (c.π.app j.left) ≫ hjX.imageι) ≫
        pullback.fst (D.map j.hom) Y₁.hom
        = pullback.snd gZ (c.π.app j.left) ≫ c.π.app j.left := by
      rw [Category.assoc]
      exact pullback.condition
    let m : pullback gZ (c.π.app j.left) ⟶
        pullback (pullback.fst (D.map j.hom) Y₁.hom) (c.π.app j.left) :=
      pullback.lift (pullback.fst gZ (c.π.app j.left) ≫ hjX.imageι)
        (pullback.snd gZ (c.π.app j.left)) wm
    have hmf : m ≫ pullback.fst (pullback.fst (D.map j.hom) Y₁.hom) (c.π.app j.left)
        = pullback.fst gZ (c.π.app j.left) ≫ hjX.imageι := pullback.lift_fst _ _ _
    have hms : m ≫ pullback.snd (pullback.fst (D.map j.hom) Y₁.hom) (c.π.app j.left)
        = pullback.snd gZ (c.π.app j.left) := pullback.lift_snd _ _ _
    have he : pullback.lift hjX.toImage f hw ≫ m = pullback.lift hjX f hwE := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hmf, pullback.lift_fst_assoc, hjX.toImage_imageι,
          pullback.lift_fst]
      · simp only [Category.assoc, hms, pullback.lift_snd]
    have hcomp : IsImmersion (pullback.lift hjX.toImage f hw ≫ m) := by
      rw [he]
      exact himmE
    exact IsImmersion.of_comp (pullback.lift hjX.toImage f hw) m
  exact hasDenseChowModification_of_baseChange f hjX.toImage gZ (c.π.app j.left) hw
    πZ iP V hπ hsurj himm hcm hViso hdense

end AlgebraicGeometry

end
