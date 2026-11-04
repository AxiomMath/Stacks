module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCoequalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# Stacks 0AGG from a finite coequalizer

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian,
and let `R = Y ×_X Y` with its projections `s, t : R ⟶ Y`. Stacks 0AGG says that `s, t` have a
coequalizer `π : Y ⟶ X'` among algebraic spaces over `S` and lists five properties of it. This
file proves that once *one* coequalizer `X'` is known whose morphism `X' ⟶ X` is finite — the
existence statement together with clause (1) — the remaining clauses hold for *every*
coequalizer, by the arguments of the source:

* clause (1) for an arbitrary coequalizer `D`: two coequalizers are isomorphic compatibly with
  the morphisms to `X`, and finiteness is stable under composition with an isomorphism;
* clause (2): `g = π ≫ (X' ⟶ X)` is proper and `X' ⟶ X`, being finite, is separated, so `π` is
  proper by Stacks 04NX;
* clause (3): `π` is scheme-theoretically dominant
  (`AlgebraicGeometry.Space.KernelPairCoequalizer.schemeTheoreticImageSubfunctor_π_eq_top`, a
  consequence of the universal property alone), so the image of `|π|` is dense (Stacks 082Z,
  `π` being quasi-compact); it is closed because `π` is universally closed. The source uses the
  Stein factorization of Stacks 0A1B here; the universal property makes it unnecessary;
* clause (4): the source's argument through Stacks 040X: `R ⟶ X' ×_X X'` is surjective, as a
  composite of two base changes of the surjective `π`, and it factors through the diagonal of
  `X' ⟶ X` because `π` equalizes `s` and `t`;
* clause (5) is `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_core`.

## Main results

* `AlgebraicGeometry.Space.KernelPairCoequalizer.spaceIso`: any two coequalizers of the kernel
  pair of `g` are isomorphic, compatibly with the quotient morphisms and the morphisms to `X`.
* `AlgebraicGeometry.Space.KernelPairCoequalizer.isProper_π_of_isFinite`,
  `AlgebraicGeometry.Space.KernelPairCoequalizer.isSurjective_π_of_isProper` and
  `AlgebraicGeometry.Space.KernelPairCoequalizer.universallyInjective_toTarget_of_isSurjective`:
  clauses (2), (3) and (4) of Stacks 0AGG, each from the one before.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_exists_isFinite`: Stacks 0AGG, from
  the existence, for every proper `g` onto a locally Noetherian algebraic space, of one
  coequalizer of the kernel pair whose morphism to the target is finite.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is a finite morphism: its base change
along a morphism from an affine object of the site is that object, with the identity as
projection. -/
theorem isFinite_of_isIso_hom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] :
    IsFinite B S hS f := by
  intro U hU ξ
  refine ⟨U, 𝟙 U, ξ ≫ inv f, hU, ?_, ?_⟩
  · rw [CategoryTheory.Functor.map_id]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsFinite (𝟙 _))
  · rw [CategoryTheory.Functor.map_id]
    exact IsPullback.of_vert_isIso ⟨by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]⟩

namespace KernelPairCoequalizer

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X}

/-! ### Uniqueness of the coequalizer -/

/-- Two coequalizers of the kernel pair of `g` are isomorphic. -/
def spaceIso (D D' : KernelPairCoequalizer B S hS g) : D.space ≅ D'.space :=
  D.isColimit.coconePointUniqueUpToIso D'.isColimit

/-- The isomorphism between two coequalizers of the kernel pair of `g` commutes with their
quotient morphisms. -/
@[reassoc (attr := simp)]
theorem π_spaceIso_hom (D D' : KernelPairCoequalizer B S hS g) :
    D.π ≫ (D.spaceIso D').hom = D'.π :=
  D.isColimit.comp_coconePointUniqueUpToIso_hom D'.isColimit WalkingParallelPair.one

/-- The isomorphism between two coequalizers of the kernel pair of `g` commutes with their
morphisms to the target. -/
@[reassoc (attr := simp)]
theorem spaceIso_hom_toTarget (D D' : KernelPairCoequalizer B S hS g) :
    (D.spaceIso D').hom ≫ D'.toTarget = D.toTarget := by
  refine Cofork.IsColimit.hom_ext D.isColimit ?_
  show D.π ≫ _ = D.π ≫ _
  rw [π_spaceIso_hom_assoc, D'.fac, D.fac]

/-- The quotient morphism followed by the morphism to the target is `g`, on the underlying
morphisms of presheaves. -/
theorem π_hom_comp_toTarget_hom (D : KernelPairCoequalizer B S hS g) :
    D.π.hom ≫ D.toTarget.hom = g.hom :=
  congrArg (fun k : Y ⟶ X => k.hom) D.fac

/-! ### Clause (1) for every coequalizer -/

/-- Finiteness of the morphism to the target passes from one coequalizer of the kernel pair to
any other: the two differ by an isomorphism over the target. -/
theorem isFinite_toTarget_of_isFinite (D D' : KernelPairCoequalizer B S hS g)
    (h : IsFinite B S hS D'.toTarget.hom) : IsFinite B S hS D.toTarget.hom := by
  have hiso : IsIso (D.spaceIso D').hom.hom :=
    ⟨(D.spaceIso D').inv.hom, congrArg (fun k => k.hom) (D.spaceIso D').hom_inv_id,
      congrArg (fun k => k.hom) (D.spaceIso D').inv_hom_id⟩
  have he : (D.spaceIso D').hom.hom ≫ D'.toTarget.hom = D.toTarget.hom :=
    congrArg (fun k => k.hom) (D.spaceIso_hom_toTarget D')
  rw [← he]
  exact isFinite_comp B S hS (isFinite_of_isIso_hom B S hS _) h

/-! ### Clause (2) -/

/-- **Stacks 0AGG, clause (2), from clause (1).** If `g` is proper and the morphism from a
coequalizer of its kernel pair to the target is finite, the quotient morphism is proper: by
Stacks 04NX, since `g` factors through it and a finite morphism is separated. -/
theorem isProper_π_of_isFinite (D : KernelPairCoequalizer B S hS g)
    (hg : IsProper B S hS g.hom) (hfin : IsFinite B S hS D.toTarget.hom) :
    IsProper B S hS D.π.hom :=
  isProper_of_comp_of_isSeparated B S hS Y.property D.space.property X.property _ _
    (by rwa [D.π_hom_comp_toTarget_hom])
    (isSeparated_of_isFinite B S hS _ D.space.property X.property hfin)

/-! ### Clause (3) -/

/-- **Stacks 0AGG, clause (3), from clause (2).** A proper quotient morphism of a coequalizer of
a kernel pair is surjective. Its scheme-theoretic image is everything, by the universal property
of the coequalizer, so the image of `|π|` is dense, `π` being quasi-compact; and it is closed,
`π` being universally closed. -/
theorem isSurjective_π_of_isProper (D : KernelPairCoequalizer B S hS g)
    (hπ : IsProper B S hS D.π.hom) : IsSurjective B S hS D.π.hom := by
  have hqc : IsQuasiCompact B S hS D.π.hom :=
    isQuasiCompact_of_universallyClosed B S hS Y.property D.space.property _ hπ.2.2
  have hiso : IsIso (schemeTheoreticImageSubfunctor B S hS D.π.hom).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 D.schemeTheoreticImageSubfunctor_π_eq_top
  have hdense : closure (Set.range (pointsMap B S hS Y.obj D.π.hom)) = Set.univ := by
    rw [← range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS _
      Y.property D.space.property hqc]
    exact Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS _)
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS Y.obj D.π.hom)) :=
    (isClosed_of_universallyClosed B S hS D.space.property _ hπ.2.2).isClosed_range
  exact Set.range_eq_univ.1 (by rw [← hclosed.closure_eq, hdense])

/-! ### Clause (4) -/

/-- The quotient morphism identifies the two projections of the presheaf fibre product
`Y ×_X Y`. -/
theorem pullback_fst_π_eq_pullback_snd_π (D : KernelPairCoequalizer B S hS g) :
    pullback.fst g.hom g.hom ≫ D.π.hom = pullback.snd g.hom g.hom ≫ D.π.hom := by
  have sq := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback g g)
  rw [← cancel_epi sq.isoPullback.hom, ← Category.assoc, sq.isoPullback_hom_fst,
    ← Category.assoc, sq.isoPullback_hom_snd]
  exact congrArg (fun k => k.hom) D.equalizes

/-- A morphism `m` between fibre products compatible with the projections is a base change of
`f` when the outer rectangle is a pullback. -/
private theorem isPullback_of_lift {𝒞 : Type*} [Category 𝒞] {A B C X P P' : 𝒞} {f : A ⟶ B}
    {h : B ⟶ X} {e : A ⟶ X} {k : C ⟶ X} {a : P' ⟶ A} {c : P' ⟶ C} {a' : P ⟶ B} {c' : P ⟶ C}
    {m : P' ⟶ P} (he : f ≫ h = e) (h₁ : IsPullback a c e k) (h₂ : IsPullback a' c' h k)
    (ha : m ≫ a' = a ≫ f) (hc : m ≫ c' = c) : IsPullback a m f a' :=
  IsPullback.of_bot (by rwa [hc, he]) ha.symm h₂

/-- **Stacks 0AGG, clause (4), from clause (3).** If the quotient morphism of a coequalizer of
the kernel pair of `g` is surjective, the morphism to the target is universally injective. By
Stacks 040X it suffices that the diagonal of `X' ⟶ X` is surjective. The morphism
`R = Y ×_X Y ⟶ X' ×_X X'` is surjective, as the composite of the two base changes
`Y ×_X Y ⟶ X' ×_X Y ⟶ X' ×_X X'` of `π`, and it factors through the diagonal because `π`
equalizes the two projections. -/
theorem universallyInjective_toTarget_of_isSurjective (D : KernelPairCoequalizer B S hS g)
    (hπ : IsSurjective B S hS D.π.hom) : UniversallyInjective B S hS D.toTarget.hom := by
  set p := D.π.hom
  set q := D.toTarget.hom
  have hfac : p ≫ q = g.hom := D.π_hom_comp_toTarget_hom
  -- `Y ×_X Y ⟶ X' ×_X Y`, a base change of `π`
  let m₁ : pullback g.hom g.hom ⟶ pullback q g.hom :=
    pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
      (by rw [Category.assoc, hfac, pullback.condition])
  have hm₁ : IsPullback (pullback.fst g.hom g.hom) m₁ p (pullback.fst q g.hom) :=
    isPullback_of_lift hfac (IsPullback.of_hasPullback g.hom g.hom)
      (IsPullback.of_hasPullback q g.hom) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  -- `X' ×_X Y ⟶ X' ×_X X'`, a base change of `π`
  let m₂ : pullback q g.hom ⟶ pullback q q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p)
      (by rw [Category.assoc, hfac, pullback.condition])
  have hm₂ : IsPullback (pullback.snd q g.hom) m₂ p (pullback.snd q q) :=
    isPullback_of_lift hfac (IsPullback.of_hasPullback q g.hom).flip
      (IsPullback.of_hasPullback q q).flip (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
  -- the composite factors through the diagonal
  have hcomp : m₁ ≫ m₂ = (pullback.fst g.hom g.hom ≫ p) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]
      exact (D.pullback_fst_π_eq_pullback_snd_π).symm
  have hsurj : Function.Surjective (pointsMap B S hS _ (pullback.diagonal q) ∘
      pointsMap B S hS _ (pullback.fst g.hom g.hom ≫ p)) := by
    rw [← pointsMap_comp, ← hcomp, pointsMap_comp]
    exact (surjective_pointsMap_of_isPullback B S hS hm₂ hπ).comp
      (surjective_pointsMap_of_isPullback B S hS hm₁ hπ)
  exact universallyInjective_of_isSurjective_diagonal B S hS q hsurj.of_comp

end KernelPairCoequalizer

/-! ### Stacks 0AGG from one finite coequalizer -/

/-- **Stacks 0AGG, from existence and clause (1).** Suppose that for every proper morphism
`g : Y ⟶ X` of algebraic spaces over `S` with `X` locally Noetherian, the kernel pair of `g`
has *some* coequalizer whose morphism to `X` is finite. Then the full conclusion of Stacks 0AGG
holds: clause (1) for every coequalizer by uniqueness of coequalizers, clause (2) by
Stacks 04NX, clause (3) from the universal property, clause (4) by Stacks 040X, and clause (5)
by `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_core`. -/
theorem properKernelPairCoequalizers_of_exists_isFinite
    (h : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
      HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
      IsProper B S hS g.hom →
      ∃ D : KernelPairCoequalizer B S hS g, IsFinite B S hS D.toTarget.hom) :
    ProperKernelPairCoequalizers B S hS := by
  have hfin : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
      HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
      IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
        IsFinite B S hS D.toTarget.hom := by
    intro X Y g hN hp D
    obtain ⟨D', hD'⟩ := h g hN hp
    exact D.isFinite_toTarget_of_isFinite D' hD'
  have hprop : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
      HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
      IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
        IsProper B S hS D.π.hom :=
    fun g hN hp D => D.isProper_π_of_isFinite hp (hfin g hN hp D)
  exact properKernelPairCoequalizers_of_core B S hS
    { nonempty_coequalizer := fun g hN hp => (h g hN hp).elim fun D _ => ⟨D⟩
      isFinite_toTarget := hfin
      isProper_π := hprop
      isSurjective_π := fun g hN hp D => D.isSurjective_π_of_isProper (hprop g hN hp D)
      universallyInjective_toTarget := fun g hN hp D =>
        D.universallyInjective_toTarget_of_isSurjective
          (D.isSurjective_π_of_isProper (hprop g hN hp D)) }

end AlgebraicGeometry.Space

end
