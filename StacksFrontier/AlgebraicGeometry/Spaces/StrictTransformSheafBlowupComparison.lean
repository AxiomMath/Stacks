module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComparisonOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# Stacks 0864, clause (2): the strict transform of a module is a direct image

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed subspace,
let `b : A' ⟶ A` be the blowup of `A` in `Z` and let `f : X ⟶ A` be an algebraic space over `A`.
Stacks 0864, clause (1) says that the strict transform `X'` of `X` — the closed subspace of
`X ×_A A'` of Stacks 0862, clause (2) — **is** the blowup of `X` in the inverse image `f⁻¹Z`;
that is `AlgebraicGeometry.Space.isBlowupAlong_strictTransform` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformIsBlowup.lean`.  Clause (2) says that for an
`𝒪_X`-module `F` the strict transform `F'` of `F` — the quotient of `pr_X^*F` by its sections
supported on the exceptional preimage, Stacks 0862, clause (1) — **is the direct image along the
closed immersion `X' ⟶ X ×_A A'` of the strict transform of `F` relative to `X' ⟶ X`.**

This file proves clause (2), with no hypothesis beyond `b` being the blowup of `A` in `Z`.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformSheafOver`: the strict transform of a module relative
  to a blowup `b'' : X'' ⟶ X` of `X` itself, that is the quotient of `b''^*F` by its sections
  supported on the exceptional divisor, read on `X''`; and
  `AlgebraicGeometry.Space.strictTransformSheafOverQuotient`, the quotient map onto it.  This is
  the strict transform of Stacks 0862, clause (1) in the case where the space being blown up and
  the space over it coincide, with the ambient base change `X ×_X X''` replaced by its canonical
  model `X''` and the projection to the source by `b''`.
* `AlgebraicGeometry.Space.strictTransformSheafPushforwardComparison`: the canonical comparison
  `pr_X^*F ⟶ i_*F''` of clause (2), for a morphism `i : X'' ⟶ X ×_A A'` over `X`.  It is the unit
  of the adjunction of Stacks 03LU followed by the direct image of the comparison
  `i^*pr_X^*F ≅ b''^*F` of Stacks 03LU and the quotient map onto the strict transform.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransformSheafIso_modulePushforward_strictTransformSpace`
  is **Stacks 0864, clause (2)**: the strict transform `F'` is isomorphic to the direct image
  along the closed immersion `X' ⟶ X ×_A A'` of the strict transform of `F` relative to the
  blowup `X' ⟶ X` of `X` in `f⁻¹Z`, by the isomorphism which carries the quotient map onto `F'`
  to the canonical comparison.  Since that quotient map is an epimorphism, the isomorphism is
  determined by that equation; this is the sense in which clause (2)'s isomorphism is canonical,
  and it is how the scheme-level `AlgebraicGeometry.exists_strictTransformSheafBlowUpIso` of
  Stacks 080E is pinned down as well.
* `AlgebraicGeometry.Space.exists_strictTransformSheafIso_modulePushforward_of_isBlowupAlong` is
  the same statement for an arbitrary `i : X'' ⟶ X ×_A A'` whose composite with the projection to
  `X` is a blowup of `X` in `f⁻¹Z`; the tagged statement is its case `i = X' ⟶ X ×_A A'`, where
  that hypothesis is clause (1).
* `AlgebraicGeometry.Space.kernelSectionsSupportedIn_of_mono_modulePullback_map`: a morphism of
  `𝒪_X`-modules whose inverse image along an étale subspace carrying every point outside a closed
  set `T` is a monomorphism kills only sections supported on `T`.  This is the form in which the
  hypothesis `hq` of `AlgebraicGeometry.Space.exists_strictTransformSheafIso` is produced by a
  geometric argument on the complement of `T`, and it generalizes
  `AlgebraicGeometry.Space.kernelSectionsSupportedIn_etaleModulePullbackAdjunction_unit`.
* `AlgebraicGeometry.Space.etaleModulePullback_supportedSectionsSubmodule_ι_eq_zero` and
  `AlgebraicGeometry.Space.isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule`: along
  an étale morphism no point of whose source lies over `T`, the sections supported on `T` restrict
  to zero, so the inverse image of the projection onto the quotient by them is invertible.
* `CategoryTheory.Adjunction.mono_map_map_unit_comp`: for an adjunction `L ⊣ R`, a morphism
  `α : L G ⟶ M` and a functor `P`, if `P α` is a monomorphism then so is the image under `P ∘ L`
  of the morphism adjunct to `α`.  This is the triangle identity doing the work of clause (2),
  stated away from the large functors of the situation.
* `CategoryTheory.mono_map_of_natIso`: being a monomorphism after a functor is invariant under a
  natural isomorphism of that functor — the monomorphism companion of
  `CategoryTheory.NatIso.isIso_map_iff`.

## Implementation notes

The isomorphism is the universal property of the supported-sections quotient,
`AlgebraicGeometry.Space.exists_strictTransformSheafIso`, applied to the canonical comparison
`q : pr_X^*F ⟶ i_*F''`.  Its three hypotheses are discharged as follows.

*The comparison is an epimorphism.*  The unit `G ⟶ i_*i^*G` of Stacks 03LU at a closed immersion
is an epimorphism, by
`AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated`
fed the essential-image clause of Stacks 08KS
(`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`); the quotient map
is one; and the direct image along a closed immersion preserves epimorphisms,
`AlgebraicGeometry.Space.preservesEpimorphisms_modulePushforward_of_isClosedImmersion`.  That `i`
is a closed immersion is clause (1), through
`AlgebraicGeometry.Space.isClosedImmersion_strictTransformBlowUpComparison`.

*The target has no sections supported on the exceptional preimage.*  This is
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections`
of `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformComparisonOffExceptional.lean`.

*The comparison kills only sections supported on the exceptional preimage.*  This is the
geometric half, and it is where clause (1)'s divisor-free content enters: over the complement
`C ⊆ X ×_A A'` of the exceptional preimage the comparison `i` is an isomorphism,
`AlgebraicGeometry.Space.isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong`.  So
the inverse image `C' = i^{-1}C` is an open subspace of `X''`
(`AlgebraicGeometry.Space.isOpenSubspace_preimage`) whose inclusion `σ : C' ⟶ X''` composed with
`i` is étale and a monomorphism, and through which every chart of `X ×_A A'` lying over `Cᶜ`
factors.  No point of `C'` lies over the exceptional divisor of `b''`, so the inverse image along
`σ` of the quotient map onto `F''` is invertible, and therefore so is the inverse image of the
morphism `i^*pr_X^*F ⟶ F''` that `q` is adjunct to; the triangle identity
(`CategoryTheory.Adjunction.mono_map_map_unit_comp`) turns that into `σ^*i^*q` being a
monomorphism, the comparison of inverse images along a composite
(`AlgebraicGeometry.Space.modulePullbackCompIso`) into `(σ ≫ i)^*q` being one, and
`AlgebraicGeometry.Space.kernelSectionsSupportedIn_of_mono_modulePullback_map` into the kernel
condition.

So neither the scheme case Stacks 080E, clause (2) nor the étale-local reduction through
Stacks 0863 is used; the argument runs inside the universal property of Stacks 085U, exactly as
clause (1) does.

**No quasi-coherence of `F` is assumed.**  The Stacks Project states clause (2) for a
quasi-coherent `F` and the argument uses nothing of `F`, as the scheme-level Stacks 080E,
clause (2) in `StacksFrontier/AlgebraicGeometry/Blowup/Transform/InverseImageCentre.lean` already
records.

**Two elaboration measurements.**  The triangle identity and the transport of a monomorphism
along a natural isomorphism are stated for an arbitrary adjunction and an arbitrary natural
isomorphism; asked for directly at the inverse and direct images of this situation, the same
equations exceed the elaborator's budget at `whnf`.  And the canonical comparison is unfolded by
`simp only` at the start of the proof rather than left to the final `exact`: the definition is
delta-reduced there by a rewrite instead of by a defeq check inside the existential statement,
which is the difference between 43 seconds and a timeout.

## References

* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- **Being a monomorphism after a functor is invariant under a natural isomorphism of that
functor.**  Stated because `CategoryTheory.NatIso.isIso_map_iff` has no monomorphism companion,
and because an instance of it at a concrete pair of large functors is otherwise assembled by
hand at every use. -/
theorem mono_map_of_natIso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {X Y : C} (φ : X ⟶ Y) (h : Mono (F.map φ)) : Mono (G.map φ) := by
  have h1 : G.map φ = (e.app X).inv ≫ F.map φ ≫ (e.app Y).hom := by
    rw [show F.map φ ≫ (e.app Y).hom = (e.app X).hom ≫ G.map φ from e.hom.naturality φ,
      Iso.inv_hom_id_assoc]
  rw [h1]
  have := h
  infer_instance

namespace Adjunction

/-- **An adjunct morphism is carried to a monomorphism by any functor which carries the morphism
it is adjunct to to one.**  For an adjunction `L ⊣ R`, a morphism `α : L G ⟶ M` and a functor `P`
out of the target category, if `P α` is a monomorphism then so is `P (L (η_G ≫ R α))`, the image
under `P ∘ L` of the morphism `G ⟶ R M` adjunct to `α`.

The two are related by one triangle identity: composing with `P` of the counit at `M` carries the
latter to the former, because `L` of the adjunct of `α` followed by the counit *is* `α`.  This is
the step that makes the kernel of the comparison of Stacks 0864, clause (2) computable on the
complement of the exceptional preimage, and it is stated here, away from the large functors of
that situation, because the same equation asked for directly at them exceeds the elaborator's
budget at `whnf`. -/
theorem mono_map_map_unit_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (P : D ⥤ E) {G : C} {M : D} (α : L.obj G ⟶ M)
    (h : Mono (P.map α)) :
    Mono (P.map (L.map (adj.unit.app G ≫ R.map α))) := by
  have key : L.map (adj.unit.app G ≫ R.map α) ≫ adj.counit.app M = α := by
    rw [Functor.map_comp, Category.assoc,
      show L.map (R.map α) ≫ adj.counit.app M = adj.counit.app (L.obj G) ≫ α from
        adj.counit.naturality α,
      ← Category.assoc]
    simp
  have hfac : P.map (L.map (adj.unit.app G ≫ R.map α)) ≫ P.map (adj.counit.app M) =
      P.map α := by
    rw [← P.map_comp, key]
  have := h
  exact mono_of_mono_fac hfac

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Supported sections against an étale morphism missing the supported set -/

/-- **Sections supported on `T` die on an étale morphism missing `T`.**  Let `σ : V ⟶ X` be an
étale morphism of algebraic spaces no point of whose source lies over a set `T` of points of
`X`.  Then the étale restriction along `σ` of the inclusion of the submodule of sections
supported on `T` is the zero morphism.

The sections of the étale restriction over a chart `U` of `V` are the sections over the
composite chart of `X`, which lies entirely over the complement of `T`; so a section supported
on `T` there has empty support and is zero by
`AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`. -/
theorem etaleModulePullback_supportedSectionsSubmodule_ι_eq_zero
    {V X : AlgebraicSpaces B S hS} (σ : V ⟶ X) (hσ : IsEtale B S hS σ.hom)
    (T : Set (points B S hS X.1))
    (hmiss : ∀ v : points B S hS V.1, pointsMap B S hS V.1 σ.hom v ∉ T)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModulePullback.{u, u} B S hS σ hσ).map
      (supportedSectionsSubmodule B S hS X.1 X.2 T M).ι = 0 := by
  ext U x
  set W : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS σ hσ).obj U.unop with hW
  have hWhom : W.1.hom = U.unop.1.hom ≫ σ.hom := rfl
  have hsupp : supportOfSection B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 M) W x.1 = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
    have hmem := (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T M W x.1).mp x.2 hy
    refine hmiss (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS V.1).obj U.unop)) U.unop.1.hom y) ?_
    have hcomp : pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom y =
        pointsMap B S hS V.1 σ.hom (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS V.1).obj U.unop)) U.unop.1.hom y) := by
      rw [hWhom]
      exact pointsMap_comp_apply B S hS U.unop.1.hom σ.hom y
    exact hcomp ▸ hmem
  exact eq_zero_of_supportOfSection_eq_empty
    (F := moduleAddSheaf B S hS X.1 X.2 M) W x.1 hsupp

/-- **The inverse image of the quotient by the sections supported on `T` is an isomorphism along
an étale morphism missing `T`.**  For `σ : V ⟶ X` étale with no point of `V` over `T`, the
inverse image along `σ` of the projection `M ⟶ M/Γ_T(M)` is invertible.

The inverse image of the inclusion of `Γ_T(M)` is zero, by
`AlgebraicGeometry.Space.etaleModulePullback_supportedSectionsSubmodule_ι_eq_zero` transported
across Stacks 03LW; and the inverse image, being a left adjoint, carries the cokernel of that
inclusion to the cokernel of zero, whose projection is invertible. -/
theorem isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule
    {V X : AlgebraicSpaces B S hS} (σ : V ⟶ X) (hσ : IsEtale B S hS σ.hom)
    (T : Set (points B S hS X.1))
    (hmiss : ∀ v : points B S hS V.1, pointsMap B S hS V.1 σ.hom v ∉ T)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((modulePullback B S hS σ).map
      (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T M).ι)) := by
  have hcolim := (modulePullbackAdjunction B S hS σ).leftAdjoint_preservesColimits.{0, 0}
  have hleft := (modulePullbackAdjunction B S hS σ).isLeftAdjoint
  have hbiprod : PreservesBinaryBiproducts (modulePullback B S hS σ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : (modulePullback B S hS σ).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  set ι := (supportedSectionsSubmodule B S hS X.1 X.2 T M).ι with hι
  have hzero : (modulePullback B S hS σ).map ι = 0 := by
    have hnat := (modulePullbackIsoEtaleModulePullback B S hS σ hσ).hom.naturality ι
    have h0 := etaleModulePullback_supportedSectionsSubmodule_ι_eq_zero B S hS σ hσ T hmiss M
    rw [hι, h0, comp_zero] at hnat
    have := (Iso.cancel_iso_hom_right _ _
      ((modulePullbackIsoEtaleModulePullback B S hS σ hσ).app M)).1
      (hnat.trans (zero_comp).symm)
    exact this
  have hπ := PreservesCokernel.π_iso_hom (modulePullback B S hS σ) ι
  have hiso : IsIso (cokernel.π ((modulePullback B S hS σ).map ι)) :=
    cokernel.π_of_zero hzero
  have : IsIso ((modulePullback B S hS σ).map (cokernel.π ι) ≫
      (PreservesCokernel.iso (modulePullback B S hS σ) ι).hom) := by
    rw [hπ]
    exact hiso
  exact IsIso.of_isIso_comp_right _
    (PreservesCokernel.iso (modulePullback B S hS σ) ι).hom

/-! ### Reading the supported-section kernel condition off an étale cover of the complement -/

/-- **A morphism whose inverse image along an étale subspace carrying every point outside `T`
is a monomorphism kills only sections supported on `T`**, for `T` closed.

This is the shape in which `AlgebraicGeometry.Space.KernelSectionsSupportedIn` is produced by a
geometric argument on the complement of `T`: the hypothesis is about the inverse image of
Stacks 03LU along `j`, which by Stacks 03LW is étale restriction, so a monomorphism there is an
injection on the sections over every chart of `X` coming from a chart of `V`.  A subchart of `W`
all of whose points lie over `Tᶜ` factors through `V` by hypothesis, hence comes from a chart of
`V` by `AlgebraicGeometry.Space.exists_factorisation_smallEtalePostcomp`, so a section killed by
the morphism dies on it; and a section dying on every such subchart is supported on `T` by
`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`.

It generalizes
`AlgebraicGeometry.Space.kernelSectionsSupportedIn_etaleModulePullbackAdjunction_unit`,
whose morphism is the unit of the restriction adjunction along `j`: there the inverse image of
the unit is a split monomorphism, by the triangle identity. -/
theorem kernelSectionsSupportedIn_of_mono_modulePullback_map
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j.hom]
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hfac : ∀ (a : BigFppfOver B S hS) (φ : yoneda.obj a ⟶ X.1),
      Set.range (pointsMap B S hS (yoneda.obj a) φ) ⊆ Tᶜ → ∃ ψ, ψ ≫ j.hom = φ)
    {F Q : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ Q)
    (hmono : Mono ((modulePullback B S hS j).map φ)) :
    KernelSectionsSupportedIn B S hS X T φ := by
  -- The étale restriction of `φ` is a monomorphism, by Stacks 03LW.
  have hmono' : Mono ((etaleModulePullback.{u, u} B S hS j hj).map φ) :=
    mono_map_of_natIso (modulePullbackIsoEtaleModulePullback B S hS j hj) φ hmono
  have hinj : ∀ U : SmallEtale B S hS V.1,
      Function.Injective (φ.val.app (op ((smallEtalePostcomp B S hS j hj).obj U))) := by
    intro U
    have := hmono'
    exact PresheafOfModules.injective_of_mono
      ((SheafOfModules.forget _).map ((etaleModulePullback.{u, u} B S hS j hj).map φ)) (op U)
  intro W s hs
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS X T hT F W s
    fun U i hi => ?_
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) ⊆ Tᶜ := by
    rintro y ⟨z, rfl⟩
    have hw : yoneda.map i.hom.left ≫ W.1.hom = U.1.hom := CostructuredArrow.w i.hom
    have hz := hi z
    rw [← hw, pointsMap_comp]
    exact hz
  obtain ⟨g, hg⟩ := hfac ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom hrange
  obtain ⟨U', m, e, he⟩ := exists_factorisation_smallEtalePostcomp B S hS j hj i g hg
  have h0 : F.val.map m.op s = 0 := by
    have hz : φ.val.app (op ((smallEtalePostcomp B S hS j hj).obj U'))
        (F.val.map m.op s) = 0 :=
      (PresheafOfModules.naturality_apply φ.val m.op s).trans
        ((congrArg (fun y => Q.val.map m.op y) hs).trans (map_zero _))
    exact hinj U' (hz.trans (map_zero _).symm)
  have hop : i.op = m.op ≫ e.op := by rw [← he]; rfl
  exact (F.val.congr_map_apply hop s).trans
    ((F.val.map_comp_apply m.op e.op s).trans
      ((congrArg (fun y => F.val.map e.op y) h0).trans (map_zero _)))

/-! ### The strict transform of a module relative to a blowup of the space itself -/

section Over

variable {X X'' : AlgebraicSpaces B S hS}

/-- **The strict transform of a module relative to a blowup of `X` itself.**  For a morphism
`b'' : X'' ⟶ X` of algebraic spaces over `S` and a closed subspace `D ⊆ X''`, the quotient of
the inverse image `b''^*F` by the submodule of those of its sections that are supported on
`|D|`.

This is the strict transform of Stacks 0862, part (1) for `b''` the blowup of `X` in a closed
subspace `Y ⊆ X` and `D = b''^{-1}Y` its exceptional divisor, read on `X''` itself: in the
notation of Stacks 0862 the space being blown up and the space over it are then both `X`, the
ambient base change `X ×_X X''` is `X''`, the projection from it to the source is `b''`, and the
preimage of the exceptional divisor is `D`.  It is `AlgebraicGeometry.Space.strictTransformSheaf`
with the ambient fibre product replaced by that canonical model. -/
noncomputable abbrev strictTransformSheafOver (b'' : X'' ⟶ X)
    (D : ClosedSubspaces B S hS X''.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS X''.1 X''.2 :=
  cokernel (supportedSectionsSubmodule B S hS X''.1 X''.2
    (subspacePointSet B S hS X''.1 D.1) ((modulePullback B S hS b'').obj F)).ι

/-- The canonical quotient map `b''^*F ⟶ F''` onto the strict transform of a module relative to
a blowup of `X` itself: the cokernel projection of the inclusion of the sections supported on
`|D|`. -/
noncomputable abbrev strictTransformSheafOverQuotient (b'' : X'' ⟶ X)
    (D : ClosedSubspaces B S hS X''.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS b'').obj F ⟶ strictTransformSheafOver B S hS b'' D F :=
  cokernel.π _

end Over

/-! ### Stacks 0864, clause (2) -/

section Clause

variable {A X A' X'' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
  (Z : ClosedSubspaces B S hS A.1)

/-- **The canonical comparison of Stacks 0864, clause (2).**  For a morphism
`i : X'' ⟶ X ×_A A'` over `X`, the morphism `pr_X^*F ⟶ i_*F''` from the ambient inverse image of
an `𝒪_X`-module `F` to the direct image along `i` of the strict transform of `F` relative to
`b'' = i ≫ pr_X`: the unit of the adjunction of Stacks 03LU at `pr_X^*F`, followed by the direct
image of the comparison `i^*pr_X^*F ≅ b''^*F` of Stacks 03LU and the quotient map onto the strict
transform.

For `i` the closed immersion of the strict transform of `X` this is the comparison that clause
(2) asserts to be an isomorphism. -/
noncomputable def strictTransformSheafPushforwardComparison
    (i : X'' ⟶ strictTransformPullback B S hS f b) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F ⟶
      (modulePushforward B S hS i).obj
        (strictTransformSheafOver B S hS
          (i ≫ strictTransformPullbackToSource B S hS f b)
          (preimageClosedSubspace (i ≫ strictTransformPullbackToSource B S hS f b)
            (preimageClosedSubspace f Z)) F) :=
  (modulePullbackAdjunction B S hS i).unit.app
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) ≫
    (modulePushforward B S hS i).map
      ((modulePullbackCompIso B S hS i
            (strictTransformPullbackToSource B S hS f b)).hom.app F ≫
        strictTransformSheafOverQuotient B S hS _ _ F)

/-- **Stacks 0864, clause (2), for a morphism to the ambient base change whose composite with
the projection to `X` is a blowup of `X` in the inverse-image centre.**  Let `b : A' ⟶ A` be the
blowup of `A` in a closed subspace `Z ⊆ A`, let `f : X ⟶ A` be an algebraic space over `A`, let
`i : X'' ⟶ X ×_A A'` be a morphism for which `b'' = i ≫ pr_X` is the blowup of `X` in `f⁻¹Z`,
and let `F` be an `𝒪_X`-module.  Then the strict transform `F'` of `F` is isomorphic to the
direct image along `i` of the strict transform `F''` of `F` relative to `b''`, by an isomorphism
carrying the quotient map onto `F'` to the canonical comparison
`AlgebraicGeometry.Space.strictTransformSheafPushforwardComparison`.

The isomorphism is the universal property
`AlgebraicGeometry.Space.exists_strictTransformSheafIso` applied at the comparison, whose three
hypotheses are these.

*`Epi`*: the unit of Stacks 03LU at a closed immersion is an epimorphism
(`AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated` fed the
essential-image clause of Stacks 08KS), the quotient map is one, and the direct image along a
closed immersion preserves epimorphisms; `i` is a closed immersion because it is the comparison
of clause (1).

*`hQ`*: that the direct image has no section supported on the exceptional preimage is
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections`.

*`hq`*: that the comparison kills only sections supported on the exceptional preimage is where
the geometry enters.  Over the complement of the exceptional preimage `i` is an isomorphism
(`AlgebraicGeometry.Space.isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong`),
so the inverse image of that complement in `X''` is an open subspace `C'` mapping isomorphically
to it; the inverse image along `σ : C' ⟶ X''` of the comparison is a monomorphism, because
composing it with the counit of Stacks 03LU gives the inverse image of the quotient map, which
is invertible since no point of `C'` lies over the exceptional divisor of `b''`
(`AlgebraicGeometry.Space.isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule`); and a
monomorphism there is the kernel condition by
`AlgebraicGeometry.Space.kernelSectionsSupportedIn_of_mono_modulePullback_map`.

No quasi-coherence of `F` is assumed.  The Stacks Project states clause (2) for a quasi-coherent
`F`, and the argument uses nothing of `F`: the universal property of the quotient by the
supported sections, the exactness and full faithfulness of the direct image along a closed
immersion, and the geometry of the comparison are all independent of it.  This is also how the
scheme-level `AlgebraicGeometry.exists_strictTransformSheafBlowUpIso` of Stacks 080E is
stated. -/
theorem exists_strictTransformSheafIso_modulePushforward_of_isBlowupAlong
    (i : X'' ⟶ strictTransformPullback B S hS f b) (hb : IsBlowupAlong B S hS Z b)
    (hb'' : IsBlowupAlong B S hS (preimageClosedSubspace f Z)
      (i ≫ strictTransformPullbackToSource B S hS f b))
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ∃ e : strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F ≅
        (modulePushforward B S hS i).obj
          (strictTransformSheafOver B S hS
            (i ≫ strictTransformPullbackToSource B S hS f b)
            (preimageClosedSubspace (i ≫ strictTransformPullbackToSource B S hS f b)
              (preimageClosedSubspace f Z)) F),
      strictTransformSheafQuotient B S hS f b (preimageClosedSubspace b Z).1 F ≫ e.hom =
        strictTransformSheafPushforwardComparison B S hS f b Z i F := by
  simp only [strictTransformSheafPushforwardComparison]
  have hieq : strictTransformBlowUpComparison B S hS f b Z
      (i ≫ strictTransformPullbackToSource B S hS f b) hb hb'' = i :=
    (existsUnique_strictTransformBlowUpComparison_of_isBlowupAlong B S hS f b Z
      (i ≫ strictTransformPullbackToSource B S hS f b) hb hb'').unique
      (strictTransformBlowUpComparison_comp_toSource B S hS f b Z
        (i ≫ strictTransformPullbackToSource B S hS f b) hb hb'') rfl
  -- The exceptional preimage and the exceptional divisor of `b''`.
  have hTclosed : IsClosed (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2 _
      (exceptionalPreimage_isClosedSubspace B S hS f b (preimageClosedSubspace b Z).1
        (preimageClosedSubspace b Z).2).2
  have hi : IsClosedImmersion B S hS i.hom :=
    hieq ▸ isClosedImmersion_strictTransformBlowUpComparison B S hS f b Z
      (i ≫ strictTransformPullbackToSource B S hS f b) hb hb''
  have hQ := hieq ▸ hasNoSectionsSupportedIn_modulePushforward_cokernel_supportedSections
    B S hS f b Z (i ≫ strictTransformPullbackToSource B S hS f b) hb hb''
    ((modulePullback B S hS (i ≫ strictTransformPullbackToSource B S hS f b)).obj F)
  have hpre := hieq ▸ preimage_exceptionalPreimageSet_strictTransformBlowUpComparison
    B S hS f b Z (i ≫ strictTransformPullbackToSource B S hS f b) hb hb''
  have hfromPre := hieq ▸ isIso_fromPreimage_exceptionalPreimageComplement_of_isBlowupAlong
    B S hS f b Z (i ≫ strictTransformPullbackToSource B S hS f b) hb hb''
  -- The inverse image in `X''` of the complement of the exceptional preimage.
  have hCplOpen : IsOpenSubspace B S hS (exceptionalPreimageComplement B S hS f b Z).1 :=
    (exceptionalPreimageComplement B S hS f b Z).2
  have hcplset : Set.range (pointsMap B S hS
        (exceptionalPreimageComplement B S hS f b Z).1.toFunctor
        (exceptionalPreimageComplement B S hS f b Z).1.ι) =
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)ᶜ :=
    subspacePointSet_openComplement B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageClosedSubspace B S hS f b Z)
  have hPreOpen : IsOpenSubspace B S hS
      ((exceptionalPreimageComplement B S hS f b Z).1.preimage i.hom) :=
    isOpenSubspace_preimage B S hS i.hom (exceptionalPreimageComplement B S hS f b Z).1
      (strictTransformPullback B S hS f b).2 X''.2 hCplOpen
  set C' : AlgebraicSpaces B S hS :=
    ⟨((exceptionalPreimageComplement B S hS f b Z).1.preimage i.hom).toFunctor, hPreOpen.1⟩
    with hC'
  set σ : C' ⟶ X'' :=
    ObjectProperty.homMk ((exceptionalPreimageComplement B S hS f b Z).1.preimage i.hom).ι
    with hσ
  have hσE : IsEtale B S hS σ.hom := isEtale_ι_of_isOpenSubspace hPreOpen
  -- No point of `C'` lies over the exceptional divisor of `b''`.
  have hmiss : ∀ v : points B S hS C'.1, pointsMap B S hS C'.1 σ.hom v ∉
      subspacePointSet B S hS X''.1
        (preimageClosedSubspace (i ≫ strictTransformPullbackToSource B S hS f b)
          (preimageClosedSubspace f Z)).1 := by
    intro v hv
    have hrange : Set.range (pointsMap B S hS
          ((exceptionalPreimageComplement B S hS f b Z).1.preimage i.hom).toFunctor
          ((exceptionalPreimageComplement B S hS f b Z).1.preimage i.hom).ι) =
        pointsMap B S hS X''.1 i.hom ⁻¹'
          Set.range (pointsMap B S hS (exceptionalPreimageComplement B S hS f b Z).1.toFunctor
            (exceptionalPreimageComplement B S hS f b Z).1.ι) :=
      range_pointsMap_preimage_ι B S hS i.hom (exceptionalPreimageComplement B S hS f b Z).1
    have hmem : pointsMap B S hS C'.1 σ.hom v ∈
        pointsMap B S hS X''.1 i.hom ⁻¹'
          Set.range (pointsMap B S hS (exceptionalPreimageComplement B S hS f b Z).1.toFunctor
            (exceptionalPreimageComplement B S hS f b Z).1.ι) :=
      hrange ▸ Set.mem_range_self v
    rw [hcplset] at hmem
    have hv' : pointsMap B S hS C'.1 σ.hom v ∈
        pointsMap B S hS X''.1 i.hom ⁻¹'
          exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1 := by
      rw [hpre]
      exact hv
    exact hmem hv'
  -- The inclusion of that inverse image into the ambient base change is étale and a
  -- monomorphism, and every chart over the complement factors through it.
  have hjhom : (σ ≫ i).hom =
      (exceptionalPreimageComplement B S hS f b Z).1.fromPreimage i.hom ≫
        (exceptionalPreimageComplement B S hS f b Z).1.ι :=
    (Subfunctor.fromPreimage_ι _ _).symm
  have := hfromPre
  have hjE : IsEtale B S hS (σ ≫ i).hom := by
    rw [hjhom]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
      (isEtale_ι_of_isOpenSubspace hCplOpen)
  have hjM : Mono (σ ≫ i).hom := by
    rw [hjhom]
    have := mono_of_presheaf_isOpenImmersion hCplOpen.2
    exact mono_comp' (IsIso.mono_of_iso _) inferInstance
  have hfac : ∀ (a : BigFppfOver B S hS)
      (φ : yoneda.obj a ⟶ (strictTransformPullback B S hS f b).1),
      Set.range (pointsMap B S hS (yoneda.obj a) φ) ⊆
        (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)ᶜ →
      ∃ ψ, ψ ≫ (σ ≫ i).hom = φ := by
    intro a φ hφ
    obtain ⟨ψ, hψ⟩ := (factorsThrough_openSubspace_iff_points B S hS
      (strictTransformPullback B S hS f b).2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS a)
      (exceptionalPreimageComplement B S hS f b Z).1 hCplOpen φ).2 (by
        rw [hcplset]
        exact hφ)
    refine ⟨ψ ≫ inv ((exceptionalPreimageComplement B S hS f b Z).1.fromPreimage i.hom), ?_⟩
    rw [hjhom, Category.assoc, ← Category.assoc
      (inv ((exceptionalPreimageComplement B S hS f b Z).1.fromPreimage i.hom)),
      IsIso.inv_hom_id, Category.id_comp]
    exact hψ
  -- The canonical comparison, with its two factors named.
  set D'' : ClosedSubspaces B S hS X''.1 :=
    preimageClosedSubspace (i ≫ strictTransformPullbackToSource B S hS f b)
      (preimageClosedSubspace f Z) with hD''
  set α : (modulePullback B S hS i).obj
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) ⟶
      strictTransformSheafOver B S hS
        (i ≫ strictTransformPullbackToSource B S hS f b) D'' F :=
    (modulePullbackCompIso B S hS i
        (strictTransformPullbackToSource B S hS f b)).hom.app F ≫
      strictTransformSheafOverQuotient B S hS
        (i ≫ strictTransformPullbackToSource B S hS f b) D'' F with hα
  set q : (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F ⟶
      (modulePushforward B S hS i).obj
        (strictTransformSheafOver B S hS
          (i ≫ strictTransformPullbackToSource B S hS f b) D'' F) :=
    (modulePullbackAdjunction B S hS i).unit.app
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) ≫
      (modulePushforward B S hS i).map α with hq
  -- `Epi q`.
  have hepi : Epi q := by
    have hunit : Epi ((modulePullbackAdjunction B S hS i).unit.app
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)) :=
      epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
        (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hM) _
    have hpe : (modulePushforward B S hS i).PreservesEpimorphisms :=
      preservesEpimorphisms_modulePushforward_of_isClosedImmersion B S hS i hi
    have hαepi : Epi α := by
      rw [hα]
      exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullbackCompIso B S hS i (strictTransformPullbackToSource B S hS f b)).app F))) inferInstance
    rw [hq]
    have := hunit
    have := hpe
    have := hαepi
    infer_instance
  -- `hq`: the comparison kills only sections supported on the exceptional preimage.
  have hker : KernelSectionsSupportedIn B S hS (strictTransformPullback B S hS f b)
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) q := by
    have := hjM
    refine kernelSectionsSupportedIn_of_mono_modulePullback_map B S hS (σ ≫ i) hjE _ hTclosed
      hfac q ?_
    -- The inverse image of `α` along `σ` is a monomorphism, both of its factors being
    -- invertible there.
    have hπiso : IsIso ((modulePullback B S hS σ).map
        (strictTransformSheafOverQuotient B S hS
          (i ≫ strictTransformPullbackToSource B S hS f b) D'' F)) :=
      isIso_modulePullback_map_cokernelπ_supportedSectionsSubmodule B S hS σ hσE _ hmiss _
    have hmonoα : Mono ((modulePullback B S hS σ).map α) := by
      rw [hα, Functor.map_comp]
      have := hπiso
      exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _
        (Iso.isIso_hom ((modulePullback B S hS σ).mapIso ((modulePullbackCompIso B S hS i (strictTransformPullbackToSource B S hS f b)).app F))))
        (IsIso.mono_of_iso _)
    -- Hence so is the inverse image of `q` along `σ ≫ i`, by the triangle identity and the
    -- comparison of inverse images along a composite.
    have h1 : Mono ((modulePullback B S hS σ).map ((modulePullback B S hS i).map q)) := by
      rw [hq]
      exact (modulePullbackAdjunction B S hS i).mono_map_map_unit_comp
        (modulePullback B S hS σ) α hmonoα
    exact mono_map_of_natIso (modulePullbackCompIso B S hS σ i) q h1
  exact exists_strictTransformSheafIso B S hS f b (preimageClosedSubspace b Z).1 F q hepi hker hQ

/-- **Stacks 0864, clause (2).**  Let `S` be a scheme, let `A` be an algebraic space over `S`,
let `Z ⊆ A` be a closed subspace, let `b : A' ⟶ A` be the blowup of `A` in `Z`, let `f : X ⟶ A`
be an algebraic space over `A` and let `F` be an `𝒪_X`-module.  Then the strict transform `F'` of
`F` — the quotient of `pr_X^*F` by its sections supported on the exceptional preimage — **is the
direct image, along the closed immersion `X' ⟶ X ×_A A'` of the strict transform of `X`, of the
strict transform of `F` relative to the blowup `X' ⟶ X` of `X` in `f⁻¹Z`.**

The isomorphism carries the quotient map onto `F'` to the canonical comparison
`AlgebraicGeometry.Space.strictTransformSheafPushforwardComparison`, and since that quotient map
is an epimorphism there is exactly one isomorphism which does; that is the sense in which the
isomorphism of clause (2) is canonical.

That `X' ⟶ X` is the blowup of `X` in `f⁻¹Z`, which is what makes the strict transform of `F`
relative to it the one clause (2) speaks of, is clause (1),
`AlgebraicGeometry.Space.isBlowupAlong_strictTransform`; the statement is otherwise
`AlgebraicGeometry.Space.exists_strictTransformSheafIso_modulePushforward_of_isBlowupAlong` at
`i` the closed immersion of the strict transform.

No hypothesis beyond `b` being the blowup of `A` in `Z` is carried: in particular no second
blowup is assumed to exist, nothing is assumed of `f`, and `F` is an arbitrary `𝒪_X`-module —
the Stacks Project states clause (2) for a quasi-coherent `F`, and the argument uses nothing of
`F`.  See the module documentation. -/
@[stacks 0864 "part (2): the strict transform of a module is the direct image, along the closed \
immersion of the strict transform of X into X ×_A A', of the strict transform of that module \
relative to the blowup X' ⟶ X, by the isomorphism carrying the quotient map onto the first to \
the canonical comparison; for an arbitrary blowup of the base, an arbitrary module, and with no \
assumed inputs"]
theorem exists_strictTransformSheafIso_modulePushforward_strictTransformSpace
    (hb : IsBlowupAlong B S hS Z b) (F : Modules.{u, u} B S hS X.1 X.2) :
    ∃ e : strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F ≅
        (modulePushforward B S hS
            (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1)).obj
          (strictTransformSheafOver B S hS
            (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
              strictTransformPullbackToSource B S hS f b)
            (preimageClosedSubspace
              (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1 ≫
                strictTransformPullbackToSource B S hS f b)
              (preimageClosedSubspace f Z)) F),
      strictTransformSheafQuotient B S hS f b (preimageClosedSubspace b Z).1 F ≫ e.hom =
        strictTransformSheafPushforwardComparison B S hS f b Z
          (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1) F :=
  exists_strictTransformSheafIso_modulePushforward_of_isBlowupAlong B S hS f b Z
    (strictTransformSpaceι B S hS f b (preimageClosedSubspace b Z).1) hb
    (isBlowupAlong_strictTransform B S hS f b Z hb) F

end Clause

end AlgebraicGeometry.Space

end
