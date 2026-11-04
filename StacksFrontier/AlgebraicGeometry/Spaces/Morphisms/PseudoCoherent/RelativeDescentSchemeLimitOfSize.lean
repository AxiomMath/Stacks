module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal

/-!
# The limit of Situation 0DKU is a limit of schemes when the index is small

In Situation 0DKU the objects of the site representing the base changes of the stages and of
the limit along an affine chart `z : yoneda Z ⟶ Y₀` form a limit cone *in the site*: the base
change of a limit of presheaves along `z` is a limit of presheaves, and the Yoneda embedding
reflects limits. When the directed index set has fewer elements than the cofinality of the
site's size cutoff, the limit of the affine schemes lies in the site and the underlying scheme
functor preserves it (Stacks 07SF), so the situation satisfies
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`.

## Main results

* `AlgebraicGeometry.Space.isLimitOfIsPullbackOfIsLimit`: in any category, the base change of a
  limit cone along a morphism to its least stage is a limit cone.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isLimitRestrict`: the limit cone restricted
  to the stages at or beyond `i₀` is a limit cone.
* `AlgebraicGeometry.Space.RelativeDescentSituation.AffineBaseChangeRepresentation.isLimit_c`:
  the cone of a representation of the base changes is a limit cone in the site, with no size
  hypothesis.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_of_size`: a situation indexed
  by a set with fewer elements than the cofinality of the site's cutoff satisfies
  `IsSchemeLimit`.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u v

namespace AlgebraicGeometry.Space

/-- **The base change of a limit cone along a morphism to its initial stage is a limit cone.**
Let `L` be a limit cone over a system `Y'` indexed by a preorder with a least element `k₀`, and
let `z : Z ⟶ Y' k₀`. A cone `c` over a system `W` whose objects are the base changes
`Y' k ×_{Y' k₀} Z` and whose vertex is `L.pt ×_{Y' k₀} Z`, compatibly with the transitions and
the legs, is a limit cone. -/
def isLimitOfIsPullbackOfIsLimit {C : Type*} [Category C] {K : Type*} [Preorder K] (k₀ : K)
    (hk₀ : ∀ k, k₀ ≤ k) {Y' : Kᵒᵖ ⥤ C} {L : Cone Y'} (hL : IsLimit L) {Z : C}
    (z : Z ⟶ Y'.obj (op k₀)) {W : Kᵒᵖ ⥤ C} (c : Cone W)
    (p : ∀ k, W.obj (op k) ⟶ Y'.obj (op k)) (q : ∀ k, W.obj (op k) ⟶ Z)
    (hsq : ∀ k, IsPullback (p k) (q k) (Y'.map (homOfLE (hk₀ k)).op) z)
    (hp : ∀ (i j : K) (h : i ≤ j), W.map (homOfLE h).op ≫ p i = p j ≫ Y'.map (homOfLE h).op)
    (hq : ∀ (i j : K) (h : i ≤ j), W.map (homOfLE h).op ≫ q i = q j)
    (pc : c.pt ⟶ L.pt) (qc : c.pt ⟶ Z) (hpt : IsPullback pc qc (L.π.app (op k₀)) z)
    (hπp : ∀ k, c.π.app (op k) ≫ p k = pc ≫ L.π.app (op k))
    (hπq : ∀ k, c.π.app (op k) ≫ q k = qc) : IsLimit c :=
  have hπ : ∀ (s : Cone W) {i j : K} (h : i ≤ j),
      s.π.app (op i) = s.π.app (op j) ≫ W.map (homOfLE h).op := fun s {i j} h => by
    have := s.π.naturality (homOfLE h).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this
  let sc : Cone W → Cone Y' := fun s =>
    { pt := s.pt
      π :=
        { app := fun k => s.π.app k ≫ p k.unop
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ f
            have h : j ≤ i := leOfHom f.unop
            have hf : f = (homOfLE h).op := Subsingleton.elim _ _
            subst hf
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            rw [hπ s h, Category.assoc, hp j i h, Category.assoc] } }
  have hw : ∀ s : Cone W, hL.lift (sc s) ≫ L.π.app (op k₀) = (s.π.app (op k₀) ≫ q k₀) ≫ z :=
    fun s => by
      have h₁ := hL.fac (sc s) (op k₀)
      have h₂ := (hsq k₀).w
      have h₃ : (homOfLE (hk₀ k₀)).op = 𝟙 (op k₀) := Subsingleton.elim _ _
      rw [h₃, Y'.map_id, Category.comp_id] at h₂
      refine h₁.trans ?_
      change s.π.app (op k₀) ≫ p k₀ = _
      rw [h₂, Category.assoc]
  have hqk : ∀ (s : Cone W) (k : K), s.π.app (op k) ≫ q k = s.π.app (op k₀) ≫ q k₀ :=
    fun s k => by rw [hπ s (hk₀ k), Category.assoc, hq]
  { lift := fun s => hpt.lift (hL.lift (sc s)) (s.π.app (op k₀) ≫ q k₀) (hw s)
    fac := fun s j => by
      induction j with
      | op k =>
        refine (hsq k).hom_ext ?_ ?_
        · rw [Category.assoc, hπp, ← Category.assoc, hpt.lift_fst]
          exact hL.fac (sc s) (op k)
        · rw [Category.assoc, hπq, hpt.lift_snd]
          exact (hqk s k).symm
    uniq := fun s m hm => by
      refine hpt.hom_ext ?_ ?_
      · rw [hpt.lift_fst]
        refine hL.hom_ext fun j => ?_
        induction j with
        | op k =>
          refine Eq.trans ?_ (hL.fac (sc s) (op k)).symm
          change (m ≫ pc) ≫ L.π.app (op k) = s.π.app (op k) ≫ p k
          rw [Category.assoc, ← hπp, ← Category.assoc, hm]
      · rw [hpt.lift_snd, ← hπq k₀, ← Category.assoc, hm] }

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- The inclusion of the stages at or beyond the chosen one into all stages. -/
abbrev laterIndexInclusion : D.LaterIndex ⥤ I :=
  (Subtype.mono_coe (fun i : I => D.i₀ ≤ i)).functor

/-- The stage at `i₀` itself, as a later stage. -/
abbrev initialLaterIndex : D.LaterIndex := ⟨D.i₀, le_rfl⟩

/-- The inclusion of the stages at or beyond `i₀` into all stages is a final functor. -/
instance final_laterIndexInclusion : D.laterIndexInclusion.Final := by
  have := D.isDirected_laterIndex
  have := D.nonempty_laterIndex
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨k, hk, hk'⟩ := directed_of (· ≤ ·) d D.i₀
  exact ⟨⟨k, hk'⟩, ⟨homOfLE hk⟩⟩

/-- **The limit cone restricted to the stages at or beyond `i₀` is a limit cone**: the
inclusion of those stages is final, because the index set is directed. -/
def isLimitRestrict : IsLimit (D.limitCone.whisker D.laterIndexInclusion.op) :=
  (Functor.Initial.isLimitWhiskerEquiv D.laterIndexInclusion.op D.limitCone).symm D.isLimit

namespace AffineBaseChangeRepresentation

variable {D} {Z : BigAffineFppf B S hS}
  {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀)}
  (R : D.AffineBaseChangeRepresentation Z z)

/-- **The Yoneda image of a representation of the base changes is a limit cone of
presheaves**: it is the base change along `z` of the limit cone restricted to the stages beyond
`i₀`. -/
def isLimitYonedaMapCone : IsLimit (yoneda.mapCone R.c) :=
  isLimitOfIsPullbackOfIsLimit (Y' := D.laterIndexInclusion.op ⋙ D.Y) D.initialLaterIndex
    (fun k => k.2) D.isLimitRestrict z (yoneda.mapCone R.c) R.p (fun k => yoneda.map (R.q k))
    R.isPullback R.map_p
    (fun i j h => (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (R.map_q i j h)))
    R.pc (yoneda.map R.qc) R.isPullback_pt R.π_p
    (fun k => (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (R.π_q k)))

/-- **The cone of a representation of the base changes is a limit cone in the site**, with no
size hypothesis: its Yoneda image is a limit of presheaves, and the Yoneda embedding reflects
limits. -/
def isLimit_c : IsLimit R.c :=
  isLimitOfReflects yoneda R.isLimitYonedaMapCone

/-- Each object of a representation of the base changes has affine underlying scheme: it
represents the base change of the affine transition morphism `Yᵢ ⟶ Y₀` along `z`. -/
theorem isAffine_W (i : D.LaterIndex) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (R.W.obj (op i))) := by
  obtain ⟨W', p', q', hpb'⟩ := D.transition_isAffine D.i₀ i.1 i.2 Z z
  let e : yoneda.obj (R.W.obj (op i)) ≅ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W') :=
    (R.isPullback i).isoIsPullback _ _ hpb'
  let e' := Yoneda.fullyFaithful.preimageIso e
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj W')) := W'.property
  exact IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map e'.hom)

end AffineBaseChangeRepresentation

end RelativeDescentSituation

section Size

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- **Situation 0DKU indexed by a small enough set is a limit of schemes on affine charts.** If
the directed index set has fewer elements than the cofinality of the site's size cutoff, then
the limit projection `Y ⟶ Y₀` is affine (Stacks 07SF, part (1)) and every representation of
the base changes along an affine chart is a limit cone of schemes: it is a limit in the site,
and the underlying scheme functor preserves limits of such small systems of affine objects. -/
theorem RelativeDescentSituation.isSchemeLimit_of_size (hI : #I < B.cutoff.ord.cof) :
    D.IsSchemeLimit := by
  have : Nonempty I := ⟨D.i₀⟩
  have hcof : ℵ₀ < B.cutoff.ord.cof := B.aleph0_lt_cutoff_cof
  have hsub : ∀ {α : Type u} [Subsingleton α], #α < B.cutoff.ord.cof := fun {α} _ =>
    (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans hcof)
  refine ⟨?_, fun Z z R => ⟨?_⟩⟩
  · have hIop : #Iᵒᵖ < B.cutoff.ord.cof := by
      rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := I)).symm]
      exact hI
    have hA := isAffineHom_limitπ B S hS D.Y hIop (fun _ _ => hsub)
      (fun {i j} f => by
        have h : j.unop ≤ i.unop := leOfHom f.unop
        have hf : f = (homOfLE h).op := Subsingleton.elim _ _
        subst hf
        exact D.transition_isAffine _ _ h) (op D.i₀)
    rw [← D.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D.Y) (op D.i₀)]
    exact isAffineHom_iso_comp (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.Y)).hom hA
  · have := D.isDirected_laterIndex
    have := D.nonempty_laterIndex
    have hJ : #D.LaterIndexᵒᵖ < B.cutoff.ord.cof := by
      rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := D.LaterIndex)).symm]
      exact (Cardinal.mk_subtype_le _).trans_lt hI
    have := BigFppfOver.preservesLimit_toScheme R.W (fun i => R.isAffine_W i.unop) hJ
    exact isLimitOfPreserves (BigFppfOver.toScheme B S hS) R.isLimit_c

end Size

end AlgebraicGeometry.Space

end
