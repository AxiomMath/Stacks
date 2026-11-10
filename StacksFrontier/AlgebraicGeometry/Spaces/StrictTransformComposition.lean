module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# The strict transform of a module under a composition of two blowups

Let `S` be a scheme, let `A` be an algebraic space over `S`, let `Z ⊆ A` be a closed
subspace and let `b : A' ⟶ A` be the blowup of `A` in `Z`.  Let `Z' ⊆ A'` be a closed
subspace and `c : A'' ⟶ A'` the blowup of `A'` in `Z'`.  Taking the strict transform of a
module twice, first along `b` and then along `c`, is taking it once along a third blowup whose
centre `Y` has `|Y| = |Z| ∪ |b|(|Z'|)`.  This file proves the comparison of the two modules,
together with its compatibility with the quotient maps onto them, which is the content of part
(1) of Stacks 0868; the identification of the two ambient base changes and its compatibility
with the projections are in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean`, where the tag is
registered.

## Main results

* `AlgebraicGeometry.Space.exists_iteratedSupportedQuotient_iso` is the comparison in the form
  it is proved in, for an arbitrary morphism `qq : Q ⟶ P₁` of algebraic spaces, an arbitrary
  closed `T₁` downstairs and an arbitrary closed `T₂` upstairs, under one geometric hypothesis:
  that the part of `Q` lying off `T₂` is étale over `P₁`.  Then the quotient of `qq^*N` by its
  sections supported on `|qq|⁻¹T₁ ∪ T₂` is the quotient by its sections supported on `T₂` of
  the pullback of the quotient of `N` by its sections supported on `T₁`, **by the isomorphism
  carrying the projection onto the first to the composite of the two projections onto the
  second**; since the projections are epimorphisms there is exactly one isomorphism which does,
  so the comparison is canonical and not merely some isomorphism of the two quotients.
* `AlgebraicGeometry.Space.exists_iteratedStrictTransformSheaf_iso` is the same statement, with
  the same compatibility, read through
  `AlgebraicGeometry.Space.strictTransformSheaf`, for the second blowup `c` and its
  exceptional divisor.
* `AlgebraicGeometry.Space.exceptionalPreimageSet_compositeCentre` discharges the hypothesis on
  the supported sets for a composition of blowups: the exceptional preimage of the composite
  centre is the union of the inverse image of the first exceptional preimage and the exceptional
  preimage of the second centre.
* `AlgebraicGeometry.Space.injOn_pointsMap_of_isBlowupAlong`: a blowup is injective on the
  points lying off its centre.  This is the point-set content of Stacks 085T, part (1), and it
  is what makes the previous item true.
* `AlgebraicGeometry.Space.isEtale_offExceptional_toSource`: off the exceptional divisor of the
  second blowup, the projection of the ambient base change `(X ×_A A') ×_{A'} A''` to
  `X ×_A A'` is étale — the geometric input of the whole comparison, and again Stacks 085T,
  part (1).

## Implementation notes

The argument is the one the Stacks Project runs for schemes, Divisors, Lemma 31.34.6
(Stacks 080I), transported to the small étale site; its scheme-level rendering in this library
is `Stacks.StrictTransform.strictTransformSheaf_comp_blowUp`.  Both quotient maps out of
`qq^*N` are epimorphisms, and the comparison is that they have the same kernel, which is the
universal property `AlgebraicGeometry.Space.exists_supportedQuotientIso`.  That universal
property delivers the isomorphism together with its compatibility with the two quotient maps,
which is what the statements below carry: the isomorphism is the one determined by that
compatibility.  Three things have to
be checked of the composite `qq^*N → qq^*(N/Γ_{T₁}N) → qq^*(N/Γ_{T₁}N)/Γ_{T₂}(…)`.

* Its target has no nonzero local section supported on `|qq|⁻¹T₁ ∪ T₂`.  Over the part of `Q`
  lying off `T₂` the pullback `qq^*(N/Γ_{T₁}N)` is an étale pullback of `N/Γ_{T₁}N`, which has
  no nonzero section supported on `T₁`; so the sections supported on the union are those
  supported on `T₂` alone, by
  `AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq_of_isEtale`, and then the target is
  a quotient by exactly those, which has no sections supported there by
  `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule`.
* It kills only sections supported on the union.  A section it kills dies, off the union, after
  the first pullback already, because over the part of `Q` lying off the union no point lies
  over `T₁`, so `qq^*(N → N/Γ_{T₁}N)` is invertible there
  (`AlgebraicGeometry.Space.isIso_etaleModulePullback_map_modulePullback_map_cokernelProjection`).
* It is an epimorphism, the pullback being a left adjoint.

The geometric input enters once: `c` is an isomorphism over the complement of `Z'`
(`AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`, Stacks 085T part (1)), so the
inverse image of that complement is étale over `A'`, and the part of the ambient base change
lying over it — which is exactly the part lying off the exceptional preimage — is its base
change, hence étale over `X ×_A A'`.  The same tag, read on points, gives injectivity of `|b|`
off `|Z|` and with it the splitting of the supported set of the composite centre.

## References

* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {P₁ A' A'' : AlgebraicSpaces B S hS} (w : P₁ ⟶ A') (c : A'' ⟶ A')
variable (Z' : ClosedSubspaces B S hS A'.1)

/-! ### Off the exceptional divisor of the second blowup -/

/-- The inverse image in `A''` of the open complement of the centre `Z'` of the second
blowup. -/
abbrev offCentrePreimage : Subfunctor A''.1 :=
  (openComplementOfClosedSubspace B S hS A' Z').1.preimage c.hom

/-- The part of the ambient base change `P₁ ×_{A'} A''` lying over
`AlgebraicGeometry.Space.offCentrePreimage`, that is, off the exceptional preimage of the
second blowup. -/
abbrev offExceptional : Subfunctor (strictTransformPullback B S hS w c).1 :=
  (offCentrePreimage B S hS c Z').preimage
    (strictTransformPullbackToBlowUp B S hS w c).hom

/-- The inverse image of the complement of the centre is an open subspace of `A''`. -/
theorem isOpenSubspace_offCentrePreimage :
    IsOpenSubspace B S hS (offCentrePreimage B S hS c Z') :=
  isOpenSubspace_preimage B S hS c.hom _ A'.2 A''.2
    (openComplementOfClosedSubspace B S hS A' Z').2

/-- The part of the ambient base change lying off the exceptional preimage is an open
subspace of it. -/
theorem isOpenSubspace_offExceptional :
    IsOpenSubspace B S hS (offExceptional B S hS w c Z') :=
  isOpenSubspace_preimage B S hS _ _ A''.2 (strictTransformPullback B S hS w c).2
    (isOpenSubspace_offCentrePreimage B S hS c Z')

/-- **Its points are exactly those off the exceptional preimage.**  Both sides are computed by
`AlgebraicGeometry.Space.range_pointsMap_preimage_ι` as inverse images of the points of `Z'`,
the complement of a closed subspace having the complementary points by
`AlgebraicGeometry.Space.subspacePointSet_openComplement`. -/
theorem range_pointsMap_offExceptional_ι :
    Set.range (pointsMap B S hS (offExceptional B S hS w c Z').toFunctor
        (offExceptional B S hS w c Z').ι) =
      (exceptionalPreimageSet B S hS w c (Z'.1.preimage c.hom))ᶜ := by
  rw [exceptionalPreimageSet_eq_preimage]
  change Set.range (pointsMap B S hS _ ((offCentrePreimage B S hS c Z').preimage
    (strictTransformPullbackToBlowUp B S hS w c).hom).ι) = _
  rw [range_pointsMap_preimage_ι, range_pointsMap_preimage_ι, range_pointsMap_preimage_ι]
  have hc0 : Set.range (pointsMap B S hS (openComplementOfClosedSubspace B S hS A' Z').1.toFunctor
      (openComplementOfClosedSubspace B S hS A' Z').1.ι) =
      (Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι))ᶜ :=
    subspacePointSet_openComplement B S hS A' Z'
  rw [hc0, Set.preimage_compl, Set.preimage_compl]


/-- **Off the exceptional divisor of the second blowup, the ambient base change is étale over
`P₁`.**  The blowup `c` is an isomorphism over the complement of its centre (Stacks 085T,
part (1)), so the inverse image of that complement is étale over `A'`; the part of
`P₁ ×_{A'} A''` lying over it is the base change of that morphism along `P₁ ⟶ A'`, by pasting
the cartesian square of the inverse image with the cartesian square of the base change, and a
base change of an étale morphism is étale (Stacks 03FU). -/
theorem isEtale_offExceptional_toSource (hc : IsBlowupAlong B S hS Z' c) :
    IsEtale B S hS ((offExceptional B S hS w c Z').ι ≫
      (strictTransformPullbackToSource B S hS w c).hom) := by
  have hiso : IsIso ((openComplementOfClosedSubspace B S hS A' Z').1.fromPreimage c.hom) :=
    isIso_fromPreimage_openComplement hc
  have hbase : IsEtale B S hS ((offCentrePreimage B S hS c Z').ι ≫ c.hom) := by
    rw [← (Subfunctor.isPullback_preimage c.hom
      (openComplementOfClosedSubspace B S hS A' Z').1).w]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
      (isEtale_ι_of_isOpenSubspace (openComplementOfClosedSubspace B S hS A' Z').2)
  have hUopen := isOpenSubspace_offCentrePreimage B S hS c Z'
  have hVopen := isOpenSubspace_offExceptional B S hS w c Z'
  have sq1 : IsPullback (offExceptional B S hS w c Z').ι
      ((offCentrePreimage B S hS c Z').fromPreimage
        (strictTransformPullbackToBlowUp B S hS w c).hom)
      (strictTransformPullbackToBlowUp B S hS w c).hom
      (offCentrePreimage B S hS c Z').ι :=
    (Subfunctor.isPullback_preimage (strictTransformPullbackToBlowUp B S hS w c).hom
      (offCentrePreimage B S hS c Z')).flip
  have sq2 : IsPullback (strictTransformPullbackToSource B S hS w c).hom
      (strictTransformPullbackToBlowUp B S hS w c).hom w.hom c.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (AlgebraicSpaces.isPullback_fiberProduct B S hS w c)
  have sqp := sq1.paste_horiz sq2
  have sqA : IsPullback
      (ObjectProperty.homMk ((offCentrePreimage B S hS c Z').fromPreimage
          (strictTransformPullbackToBlowUp B S hS w c).hom) :
        (⟨(offExceptional B S hS w c Z').toFunctor, hVopen.1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(offCentrePreimage B S hS c Z').toFunctor, hUopen.1⟩)
      (ObjectProperty.homMk ((offExceptional B S hS w c Z').ι ≫
        (strictTransformPullbackToSource B S hS w c).hom))
      (ObjectProperty.homMk ((offCentrePreimage B S hS c Z').ι ≫ c.hom)) w :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sqp.flip.w)
      (by simpa using sqp.flip)
  exact isEtale_of_isPullback B S hS _ _ _ _ sqA hbase

/-- **The iterated quotient by supported sections, with both open parts given.**  This is
`AlgebraicGeometry.Space.exists_iteratedSupportedQuotient_iso` with the open part lying off the
whole supported set supplied as data rather than constructed; see that statement for what it
says and the module documentation for how it is proved. -/
theorem exists_iteratedSupportedQuotient_iso_aux
    {Vb V₂ Q P₁ : AlgebraicSpaces B S hS} (qq : Q ⟶ P₁)
    (T₁ : Set (points B S hS P₁.1)) (hT₁ : IsClosed T₁)
    (T₂ : Set (points B S hS Q.1)) (hT₂ : IsClosed T₂)
    (j₂ : V₂ ⟶ Q) (hj₂ : IsEtale B S hS j₂.hom) [Mono j₂.hom]
    (hj₂range : Set.range (pointsMap B S hS V₂.1 j₂.hom) = T₂ᶜ)
    (hj₂q : IsEtale B S hS (j₂ ≫ qq).hom)
    (hj₂fac : ∀ (A₀ : BigFppfOver B S hS) (f₀ : yoneda.obj A₀ ⟶ Q.1),
      Set.range (pointsMap B S hS (yoneda.obj A₀) f₀) ⊆ T₂ᶜ → ∃ g, g ≫ j₂.hom = f₀)
    (jb : Vb ⟶ Q) (hjb : IsEtale B S hS jb.hom) [Mono jb.hom]
    (hjbrange : Set.range (pointsMap B S hS Vb.1 jb.hom) =
      (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)ᶜ)
    (hjbq : IsEtale B S hS (jb ≫ qq).hom)
    (hjbfac : ∀ (A₀ : BigFppfOver B S hS) (f₀ : yoneda.obj A₀ ⟶ Q.1),
      Set.range (pointsMap B S hS (yoneda.obj A₀) f₀) ⊆
        (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)ᶜ → ∃ g, g ≫ jb.hom = f₀)
    (N : Modules.{u, u} B S hS P₁.1 P₁.2) :
    ∃ e : cokernel (supportedSectionsSubmodule B S hS Q.1 Q.2
          (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) ((modulePullback B S hS qq).obj N)).ι ≅
        cokernel (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
          ((modulePullback B S hS qq).obj
            (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι,
      cokernel.π (supportedSectionsSubmodule B S hS Q.1 Q.2
            (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)
            ((modulePullback B S hS qq).obj N)).ι ≫ e.hom =
        (modulePullback B S hS qq).map
            (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) ≫
          cokernel.π (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
            ((modulePullback B S hS qq).obj
              (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι := by
  have hSbclosed : IsClosed (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) :=
    (hT₁.preimage ((pointTopologyFamily B S hS).continuous Q.2 P₁.2 qq.hom)).union hT₂
  have hG : HasNoSectionsSupportedIn B S hS P₁ T₁
      (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) :=
    hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule B S hS P₁ T₁ hT₁ N
  have hstar : supportedSectionsSubmodule B S hS Q.1 Q.2
        (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)
        ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι)) =
      supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
        ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι)) :=
    supportedSectionsSubmodule_union_eq_of_isEtale B S hS j₂ hj₂ _ _ hT₂ hj₂fac (by rw [hj₂range]) _
      (hasNoSectionsSupportedIn_etaleModulePullback_modulePullback B S hS j₂ hj₂ qq hj₂q T₁ _ hG)
  -- no point of `Vb` lies over `T₁`
  have hempty : pointsMap B S hS Vb.1 (jb ≫ qq).hom ⁻¹' T₁ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have hxc : pointsMap B S hS Vb.1 jb.hom x ∈
        (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)ᶜ := hjbrange ▸ Set.mem_range_self x
    refine hxc (Or.inl ?_)
    rwa [Set.mem_preimage, ← pointsMap_comp_apply]
  have hisoψ := isIso_etaleModulePullback_map_modulePullback_map_cokernelProjection
    B S hS jb hjb qq hjbq T₁ N hempty
  set ψ := (modulePullback B S hS qq).map
    (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) with hψdef
  set π₂ := cokernel.π (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
    ((modulePullback B S hS qq).obj
      (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι with hπ₂def
  -- (a) the composite is an epimorphism
  have hepiψ : Epi ψ := by
    have := (modulePullbackAdjunction B S hS qq).leftAdjoint_preservesColimits.{u, u}
    exact Functor.map_epi _ _
  have hqe : Epi (ψ ≫ π₂) := epi_comp _ _
  -- (c) the target has no sections supported on the whole set
  have hQ' : HasNoSectionsSupportedIn B S hS Q
      (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)
      (cokernel (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
        ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι) := by
    rw [← hstar]
    exact hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule B S hS Q _ hSbclosed _
  -- (b) the composite kills only sections supported on the whole set
  have hq : KernelSectionsSupportedIn B S hS Q
      (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) (ψ ≫ π₂) := by
    intro W s hs
    refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS Q _ hSbclosed _ W s
      fun U i hi => ?_
    have hrangeU : Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Q.1).obj U)) U.1.hom) ⊆
        (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)ᶜ := by
      rintro y ⟨z, rfl⟩
      have hw : yoneda.map i.hom.left ≫ W.1.hom = U.1.hom := CostructuredArrow.w i.hom
      have hz := hi z
      rw [← hw, pointsMap_comp]
      exact hz
    obtain ⟨g1, hg1⟩ := hjbfac ((SmallEtale.toOver B S hS Q.1).obj U) U.1.hom hrangeU
    obtain ⟨U', m, e1, he1⟩ := exists_factorisation_smallEtalePostcomp B S hS jb hjb i g1 hg1
    -- all points of the chart `postcomp U'` lie off the whole set
    have hpostrange : Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Q.1).obj
          ((smallEtalePostcomp B S hS jb hjb).obj U')))
        ((smallEtalePostcomp B S hS jb hjb).obj U').1.hom) ⊆
        (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)ᶜ := by
      rintro y ⟨z, rfl⟩
      have hmem : pointsMap B S hS _ ((smallEtalePostcomp B S hS jb hjb).obj U').1.hom z
          ∈ Set.range (pointsMap B S hS Vb.1 jb.hom) :=
        ⟨pointsMap B S hS _ U'.1.hom z, (pointsMap_comp_apply B S hS _ jb.hom z).symm⟩
      exact hjbrange ▸ hmem
    -- the restriction of `s` to that chart
    -- `ψ s` is supported on `T₂` because the projection kills it
    have hψs : SectionSupportedIn B S hS Q.1 Q.2 T₂
        ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι)) W
        (ψ.val.app (op W) s) :=
      kernelSectionsSupportedIn_cokernelProjection T₂ _ (ψ.val.app (op W) s) hs
    have hrestr := sectionSupportedIn_restrict m (ψ.val.app (op W) s) hψs
    have hzero : ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι)).val.map m.op
        (ψ.val.app (op W) s) = 0 := by
      refine eq_zero_of_supportOfSection_eq_empty
        (F := moduleAddSheaf B S hS Q.1 Q.2 ((modulePullback B S hS qq).obj
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))) _ _ ?_
      refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
      exact hpostrange ⟨y, rfl⟩ (Or.inr (hrestr hy))
    have ht0' : ψ.val.app (op ((smallEtalePostcomp B S hS jb hjb).obj U'))
        (((modulePullback B S hS qq).obj N).val.map m.op s) = 0 :=
      (PresheafOfModules.naturality_apply ψ.val m.op s).trans hzero
    have := hisoψ
    have hmonoψ : Mono ((SheafOfModules.forget _).map
        ((etaleModulePullback B S hS jb hjb).map ψ)) :=
      @IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
    have hinj : Function.Injective
        (((etaleModulePullback B S hS jb hjb).map ψ).val.app (op U')) :=
      PresheafOfModules.injective_of_mono
        ((SheafOfModules.forget _).map ((etaleModulePullback B S hS jb hjb).map ψ)) (op U')
    have ht0 : ((modulePullback B S hS qq).obj N).val.map m.op s = 0 :=
      hinj (ht0'.trans (map_zero _).symm)
    have hop : i.op = m.op ≫ e1.op := by rw [← he1]; rfl
    exact ((((modulePullback B S hS qq).obj N).val.congr_map_apply hop s).trans
      ((((modulePullback B S hS qq).obj N).val.map_comp_apply m.op e1.op s).trans
        ((congrArg (fun y => ((modulePullback B S hS qq).obj N).val.map e1.op y) ht0).trans
          (map_zero _))))
  exact exists_supportedQuotientIso
    (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) (ψ ≫ π₂) hqe hq hQ'

/-! ### The open part lying off a closed set of points -/

section OpenOff

variable (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1)) (hT : IsClosed T)

/-- The open subspace of `X` whose points are those outside a closed set `T`. -/
def openOffSubspace : AlgebraicSpaces B S hS :=
  ⟨(openSubspaceOfPoints B S hS X.1 Tᶜ).toFunctor,
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl).1⟩

/-- Its inclusion into `X`. -/
def openOffSubspaceι : openOffSubspace B S hS X T hT ⟶ X :=
  ObjectProperty.homMk (openSubspaceOfPoints B S hS X.1 Tᶜ).ι

/-- Its points are exactly those outside `T`. -/
theorem range_pointsMap_openOffSubspaceι :
    Set.range (pointsMap B S hS (openOffSubspace B S hS X T hT).1
      (openOffSubspaceι B S hS X T hT).hom) = Tᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The inclusion of an open subspace is a monomorphism. -/
instance mono_openOffSubspaceι : Mono (openOffSubspaceι B S hS X T hT).hom :=
  mono_of_presheaf_isOpenImmersion
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl).2

/-- The inclusion of an open subspace is étale. -/
theorem isEtale_openOffSubspaceι : IsEtale B S hS (openOffSubspaceι B S hS X T hT).hom :=
  isEtale_ι_of_isOpenSubspace (isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl)

/-- A morphism into `X` all of whose points lie outside `T` factors through the open part
lying off `T`, by the order isomorphism of Stacks 03BZ. -/
theorem factorsThrough_openOffSubspace {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X.1)
    (hf : Set.range (pointsMap B S hS Y f) ⊆ Tᶜ) :
    ∃ g, g ≫ (openOffSubspaceι B S hS X T hT).hom = f :=
  (factorsThrough_openSubspace_iff_points B S hS X.2 hY _
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 Tᶜ hT.isOpen_compl) f).2
    (by rw [range_pointsMap_ι_openSubspaceOfPoints]; exact hf)

end OpenOff

/-- **The quotient by the sections supported on a union is the iterated quotient.**  Let
`qq : Q ⟶ P₁` be a morphism of algebraic spaces over `S`, let `T₁` be a closed set of points of
`P₁` and `T₂` a closed set of points of `Q`, and suppose the part of `Q` lying off `T₂` — given
here as an étale monomorphism `j₂ : V₂ ⟶ Q` with those points, through which every morphism
from an algebraic space with those points factors — is étale over `P₁`.  Then for every
`𝒪_{P₁}`-module `N` the quotient of `qq^*N` by its sections supported on `|qq|⁻¹T₁ ∪ T₂` is the
quotient, by its sections supported on `T₂`, of the pullback along `qq` of the quotient of `N`
by its sections supported on `T₁`.

See the module documentation for the three steps. -/
theorem exists_iteratedSupportedQuotient_iso
    {V₂ Q P₁ : AlgebraicSpaces B S hS} (qq : Q ⟶ P₁)
    (T₁ : Set (points B S hS P₁.1)) (hT₁ : IsClosed T₁)
    (T₂ : Set (points B S hS Q.1)) (hT₂ : IsClosed T₂)
    (j₂ : V₂ ⟶ Q) (hj₂ : IsEtale B S hS j₂.hom) [Mono j₂.hom]
    (hj₂range : Set.range (pointsMap B S hS V₂.1 j₂.hom) = T₂ᶜ)
    (hj₂q : IsEtale B S hS (j₂ ≫ qq).hom)
    (hj₂fac : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      ∀ f : Y ⟶ Q.1, Set.range (pointsMap B S hS Y f) ⊆ T₂ᶜ → ∃ g, g ≫ j₂.hom = f)
    (N : Modules.{u, u} B S hS P₁.1 P₁.2) :
    ∃ e : cokernel (supportedSectionsSubmodule B S hS Q.1 Q.2
          (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) ((modulePullback B S hS qq).obj N)).ι ≅
        cokernel (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
          ((modulePullback B S hS qq).obj
            (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι,
      cokernel.π (supportedSectionsSubmodule B S hS Q.1 Q.2
            (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂)
            ((modulePullback B S hS qq).obj N)).ι ≫ e.hom =
        (modulePullback B S hS qq).map
            (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) ≫
          cokernel.π (supportedSectionsSubmodule B S hS Q.1 Q.2 T₂
            ((modulePullback B S hS qq).obj
              (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι))).ι := by
  have hSbclosed : IsClosed (pointsMap B S hS Q.1 qq.hom ⁻¹' T₁ ∪ T₂) :=
    (hT₁.preimage ((pointTopologyFamily B S hS).continuous Q.2 P₁.2 qq.hom)).union hT₂
  have hjbE := isEtale_openOffSubspaceι B S hS Q _ hSbclosed
  have hjbrange := range_pointsMap_openOffSubspaceι B S hS Q _ hSbclosed
  obtain ⟨g1, hg1⟩ := hj₂fac (openOffSubspace B S hS Q _ hSbclosed).2
    (openOffSubspaceι B S hS Q _ hSbclosed).hom
    (by rw [hjbrange]; exact Set.compl_subset_compl.2 Set.subset_union_right)
  have hg1E : IsEtale B S hS g1 :=
    isEtale_of_comp_mono B S hS g1 j₂.hom (by rw [hg1]; exact hjbE)
  have hjbq : IsEtale B S hS ((openOffSubspaceι B S hS Q _ hSbclosed) ≫ qq).hom := by
    change IsEtale B S hS ((openOffSubspaceι B S hS Q _ hSbclosed).hom ≫ qq.hom)
    rw [← hg1, Category.assoc]
    exact isEtale_comp B S hS hg1E hj₂q
  exact exists_iteratedSupportedQuotient_iso_aux B S hS qq T₁ hT₁ T₂ hT₂ j₂ hj₂ hj₂range hj₂q
    (fun A₀ f₀ hf₀ => hj₂fac (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A₀) f₀ hf₀)
    (openOffSubspaceι B S hS Q _ hSbclosed) hjbE hjbrange hjbq
    (fun A₀ f₀ hf₀ => factorsThrough_openOffSubspace B S hS Q _ hSbclosed
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A₀) f₀ hf₀) N

/-! ### The iterated strict transform of a module -/

/-- The part of the ambient base change lying off the exceptional divisor of `c`, as an
algebraic space. -/
def offExceptionalSpace : AlgebraicSpaces B S hS :=
  ⟨(offExceptional B S hS w c Z').toFunctor, (isOpenSubspace_offExceptional B S hS w c Z').1⟩

/-- Its open immersion into the ambient base change. -/
def offExceptionalι :
    offExceptionalSpace B S hS w c Z' ⟶ strictTransformPullback B S hS w c :=
  ObjectProperty.homMk (offExceptional B S hS w c Z').ι

/-- It is a monomorphism, being the inclusion of an open subspace. -/
instance mono_offExceptionalι : Mono (offExceptionalι B S hS w c Z').hom :=
  mono_of_presheaf_isOpenImmersion (isOpenSubspace_offExceptional B S hS w c Z').2

/-- It is étale, being the inclusion of an open subspace. -/
theorem isEtale_offExceptionalι : IsEtale B S hS (offExceptionalι B S hS w c Z').hom :=
  isEtale_ι_of_isOpenSubspace (isOpenSubspace_offExceptional B S hS w c Z')

/-- Its points are those off the exceptional preimage of the second blowup. -/
theorem range_pointsMap_offExceptionalι :
    Set.range (pointsMap B S hS (offExceptionalSpace B S hS w c Z').1
      (offExceptionalι B S hS w c Z').hom) =
      (exceptionalPreimageSet B S hS w c (Z'.1.preimage c.hom))ᶜ :=
  range_pointsMap_offExceptional_ι B S hS w c Z'

/-- A morphism into the ambient base change all of whose points lie off the exceptional
preimage factors through that open part. -/
theorem factorsThrough_offExceptional {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ (strictTransformPullback B S hS w c).1)
    (hf : Set.range (pointsMap B S hS Y f) ⊆
      (exceptionalPreimageSet B S hS w c (Z'.1.preimage c.hom))ᶜ) :
    ∃ g, g ≫ (offExceptionalι B S hS w c Z').hom = f :=
  (factorsThrough_openSubspace_iff_points B S hS (strictTransformPullback B S hS w c).2 hY _
    (isOpenSubspace_offExceptional B S hS w c Z') f).2
    (by rw [range_pointsMap_offExceptional_ι]; exact hf)

/-- The exceptional preimage of the second blowup is a closed set of points, being the point
set of a closed subspace. -/
theorem isClosed_exceptionalPreimageSet_preimage :
    IsClosed (exceptionalPreimageSet B S hS w c (Z'.1.preimage c.hom)) :=
  isClosed_range_pointsMap_of_isClosedImmersion B S hS
    (strictTransformPullback B S hS w c).2 _
    (exceptionalPreimage_isClosedSubspace B S hS w c _
      (isClosedSubspace_preimage B S hS c.hom Z'.1 A'.2 A''.2 Z'.2)).2

/-- **The iterated strict transform of a module.**  Let `c : A'' ⟶ A'` be the blowup of `A'` in
a closed subspace `Z'`, let `w : P₁ ⟶ A'` be an algebraic space over `A'` and let `N` be an
`𝒪_{P₁}`-module.  Let `E''` be a subfunctor of `A''` whose exceptional preimage in
`P₁ ×_{A'} A''` is the union of the inverse image of a closed `T₁ ⊆ |P₁|` and the exceptional
preimage of `c⁻¹Z'`.  Then the strict transform of `N` with respect to `(c, E'')` is the strict
transform with respect to `(c, c⁻¹Z')` of the quotient of `N` by its sections supported on
`T₁`, by the isomorphism carrying the quotient map onto the former to the pullback of the
quotient of `N` followed by the quotient map onto the latter.  The quotient maps being
epimorphisms, exactly one isomorphism does that.

This is `AlgebraicGeometry.Space.exists_iteratedSupportedQuotient_iso` read through
`AlgebraicGeometry.Space.strictTransformSheaf`, the open part off the exceptional preimage
being `AlgebraicGeometry.Space.offExceptionalι`. -/
theorem exists_iteratedStrictTransformSheaf_iso (hc : IsBlowupAlong B S hS Z' c)
    (E'' : Subfunctor A''.1) (T₁ : Set (points B S hS P₁.1)) (hT₁ : IsClosed T₁)
    (N : Modules.{u, u} B S hS P₁.1 P₁.2)
    (hunion : exceptionalPreimageSet B S hS w c E'' =
      pointsMap B S hS (strictTransformPullback B S hS w c).1
          (strictTransformPullbackToSource B S hS w c).hom ⁻¹' T₁ ∪
        exceptionalPreimageSet B S hS w c (Z'.1.preimage c.hom)) :
    ∃ e : strictTransformSheaf B S hS w c E'' N ≅
        strictTransformSheaf B S hS w c (Z'.1.preimage c.hom)
          (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι),
      strictTransformSheafQuotient B S hS w c E'' N ≫ e.hom =
        (modulePullback B S hS (strictTransformPullbackToSource B S hS w c)).map
            (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) ≫
          strictTransformSheafQuotient B S hS w c (Z'.1.preimage c.hom)
            (cokernel (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T₁ N).ι) := by
  have key := exists_iteratedSupportedQuotient_iso B S hS
    (strictTransformPullbackToSource B S hS w c) T₁ hT₁ _
    (isClosed_exceptionalPreimageSet_preimage B S hS w c Z')
    (offExceptionalι B S hS w c Z') (isEtale_offExceptionalι B S hS w c Z')
    (range_pointsMap_offExceptionalι B S hS w c Z')
    (isEtale_offExceptional_toSource B S hS w c Z' hc)
    (fun hY f hf => factorsThrough_offExceptional B S hS w c Z' hY f hf) N
  rw [← hunion] at key
  exact key

/-! ### The composite centre -/

/-- **A blowup is injective on the points lying off its centre.**  This is the point-set
content of Stacks 085T, part (1): the inverse image of the complement of the centre maps
isomorphically to that complement, and the inclusion of an open subspace is injective on points
(Stacks 03BZ through `AlgebraicGeometry.Space.injective_pointsMap_of_isImmersion`). -/
theorem injOn_pointsMap_of_isBlowupAlong {A A₁ : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS A.1} {b : A₁ ⟶ A} (hb : IsBlowupAlong B S hS Z b) :
    Set.InjOn (pointsMap B S hS A₁.1 b.hom)
      (pointsMap B S hS A₁.1 b.hom ⁻¹'
        (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ) := by
  set U := openComplementOfClosedSubspace B S hS A Z with hU
  have hUpts : Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) =
      (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ :=
    subspacePointSet_openComplement B S hS A Z
  have hUinj : Function.Injective (pointsMap B S hS U.1.toFunctor U.1.ι) :=
    injective_pointsMap_of_isImmersion B S hS A.2 U.1.ι
      (isImmersion_of_isOpenImmersion B S hS U.2.2)
  have hiso : IsIso (U.1.fromPreimage b.hom) := isIso_fromPreimage_openComplement hb
  have hsq : (U.1.preimage b.hom).ι ≫ b.hom = U.1.fromPreimage b.hom ≫ U.1.ι :=
    ((Subfunctor.isPullback_preimage b.hom U.1).w).symm
  have hrange : Set.range (pointsMap B S hS (U.1.preimage b.hom).toFunctor
        (U.1.preimage b.hom).ι) =
      pointsMap B S hS A₁.1 b.hom ⁻¹'
        (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ := by
    rw [← hUpts]
    exact range_pointsMap_preimage_ι B S hS b.hom U.1
  have hpinj : Function.Injective
      (pointsMap B S hS (U.1.preimage b.hom).toFunctor (U.1.fromPreimage b.hom)) := by
    have hcancel : ∀ z, pointsMap B S hS U.1.toFunctor (inv (U.1.fromPreimage b.hom))
        (pointsMap B S hS (U.1.preimage b.hom).toFunctor (U.1.fromPreimage b.hom) z) = z := by
      intro z
      rw [← pointsMap_comp_apply, IsIso.hom_inv_id, pointsMap_id, id_eq]
    exact fun x y hxy => ((hcancel x).symm.trans (congrArg _ hxy)).trans (hcancel y)
  have key0 := pointsMap_apply_comm B S hS hsq
  intro t₁ ht₁ t₂ ht₂ hb12
  rw [← hrange] at ht₁ ht₂
  obtain ⟨u₁, hu₁⟩ := ht₁
  obtain ⟨u₂, hu₂⟩ := ht₂
  have key : pointsMap B S hS (U.1.preimage b.hom).toFunctor (U.1.fromPreimage b.hom) u₁ =
      pointsMap B S hS (U.1.preimage b.hom).toFunctor (U.1.fromPreimage b.hom) u₂ :=
    hUinj (((key0 u₁).symm.trans (by rw [hu₁, hb12, ← hu₂])).trans (key0 u₂))
  rw [← hu₁, ← hu₂, hpinj key]

/-- **The condition on the third centre of Stacks 0868, read on inverse images.**  If the
points of `Y` are those of `Z` together with the image of the points of `Z₁ ⊆ A₁` under the
blowup `b : A₁ ⟶ A` of `A` in `Z`, then the inverse image of `|Y|` in `A₁` is the inverse image
of `|Z|` together with `|Z₁|`.

One inclusion is `|Z| ⊆ |Y|` and `|Z₁| ⊆ |b|⁻¹|b|(|Z₁|)`.  For the other, a point of `A₁` over
`|b|(|Z₁|)` but not over `|Z|` has the same image as a point of `|Z₁|`, which also lies off
`|b|⁻¹|Z|`, so the two coincide by
`AlgebraicGeometry.Space.injOn_pointsMap_of_isBlowupAlong`. -/
theorem preimage_range_pointsMap_compositeCentre {A A₁ : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS A.1} {b : A₁ ⟶ A} (hb : IsBlowupAlong B S hS Z b)
    (Z₁ : ClosedSubspaces B S hS A₁.1) (Y : ClosedSubspaces B S hS A.1)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A₁.1 b.hom '' Set.range (pointsMap B S hS Z₁.1.toFunctor Z₁.1.ι)) :
    pointsMap B S hS A₁.1 b.hom ⁻¹' Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      pointsMap B S hS A₁.1 b.hom ⁻¹' Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        Set.range (pointsMap B S hS Z₁.1.toFunctor Z₁.1.ι) := by
  rw [hY, Set.preimage_union]
  refine Set.Subset.antisymm (fun t ht => ?_) (fun t ht => ?_)
  · rcases ht with ht | ht
    · exact Or.inl ht
    · by_cases hZ : t ∈ pointsMap B S hS A₁.1 b.hom ⁻¹'
          Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)
      · exact Or.inl hZ
      · obtain ⟨z₁, hz₁mem, hz₁eq⟩ := ht
        refine Or.inr ?_
        have hz₁notZ : z₁ ∈ pointsMap B S hS A₁.1 b.hom ⁻¹'
            (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ := by
          rw [Set.mem_preimage, hz₁eq]
          exact hZ
        have htnotZ : t ∈ pointsMap B S hS A₁.1 b.hom ⁻¹'
            (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ := hZ
        exact injOn_pointsMap_of_isBlowupAlong B S hS hb hz₁notZ htnotZ hz₁eq ▸ hz₁mem
  · rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨t, ht, rfl⟩

/-- The two readings of an inverse image from the common base agree on the ambient base
change. -/
theorem preimage_pointsMap_toSource_eq_preimage_toBlowUp
    (X₀ : Set (points B S hS A'.1)) :
    pointsMap B S hS (strictTransformPullback B S hS w c).1
        (strictTransformPullbackToSource B S hS w c).hom ⁻¹'
      (pointsMap B S hS P₁.1 w.hom ⁻¹' X₀) =
    pointsMap B S hS (strictTransformPullback B S hS w c).1
        (strictTransformPullbackToBlowUp B S hS w c).hom ⁻¹'
      (pointsMap B S hS A''.1 c.hom ⁻¹' X₀) := by
  rw [← Set.preimage_comp, ← Set.preimage_comp, ← pointsMap_comp, ← pointsMap_comp]
  exact congrArg (fun g => pointsMap B S hS (strictTransformPullback B S hS w c).1 g ⁻¹' X₀)
    (congrArg (fun φ : strictTransformPullback B S hS w c ⟶ A' => φ.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS w c).w)

/-- The exceptional preimage of a closed subspace is a closed set of points. -/
theorem isClosed_exceptionalPreimageSet {A X A₁ : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (b : A₁ ⟶ A) (E : Subfunctor A₁.1) (hE : IsClosedSubspace B S hS E) :
    IsClosed (exceptionalPreimageSet B S hS f b E) :=
  isClosed_range_pointsMap_of_isClosedImmersion B S hS (strictTransformPullback B S hS f b).2 _
    (exceptionalPreimage_isClosedSubspace B S hS f b E hE).2

/-- **The supported set of the composite blowup splits.**  In the situation of Stacks 0868 —
`b : A₁ ⟶ A` the blowup of `A` in `Z`, `c₂ : A₂ ⟶ A₁` a morphism, `Z₁ ⊆ A₁` a closed subspace
and `Y ⊆ A` a closed subspace with `|Y| = |Z| ∪ |b|(|Z₁|)` — the exceptional preimage of
`(c₂ ≫ b)⁻¹Y` in `(X ×_A A₁) ×_{A₁} A₂` is the union of the inverse image of the exceptional
preimage of `b⁻¹Z` and the exceptional preimage of `c₂⁻¹Z₁`.

Every set in sight is an inverse image of a set of points of `A`, `A₁` or `A₂`, so this is
`AlgebraicGeometry.Space.preimage_range_pointsMap_compositeCentre` with inverse images taken
along the two sides of the cartesian square of the ambient base change. -/
theorem exceptionalPreimageSet_compositeCentre {A X A₁ A₂ : AlgebraicSpaces B S hS}
    (f : X ⟶ A) {b : A₁ ⟶ A} (c₂ : A₂ ⟶ A₁)
    {Z : ClosedSubspaces B S hS A.1} (hb : IsBlowupAlong B S hS Z b)
    (Z₁ : ClosedSubspaces B S hS A₁.1) (Y : ClosedSubspaces B S hS A.1)
    (hY : Set.range (pointsMap B S hS Y.1.toFunctor Y.1.ι) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ∪
        pointsMap B S hS A₁.1 b.hom '' Set.range (pointsMap B S hS Z₁.1.toFunctor Z₁.1.ι)) :
    exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c₂
        (Y.1.preimage (c₂ ≫ b).hom) =
      pointsMap B S hS (strictTransformPullback B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c₂).1
          (strictTransformPullbackToSource B S hS
            (strictTransformPullbackToBlowUp B S hS f b) c₂).hom ⁻¹'
        exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom) ∪
      exceptionalPreimageSet B S hS (strictTransformPullbackToBlowUp B S hS f b) c₂
        (Z₁.1.preimage c₂.hom) := by
  rw [exceptionalPreimageSet_eq_preimage, exceptionalPreimageSet_eq_preimage,
    exceptionalPreimageSet_eq_preimage, range_pointsMap_preimage_ι, range_pointsMap_preimage_ι,
    range_pointsMap_preimage_ι,
    preimage_pointsMap_toSource_eq_preimage_toBlowUp B S hS
      (strictTransformPullbackToBlowUp B S hS f b) c₂
      (pointsMap B S hS A₁.1 b.hom ⁻¹' Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)),
    show (c₂ ≫ b).hom = c₂.hom ≫ b.hom from rfl, pointsMap_comp, Set.preimage_comp,
    preimage_range_pointsMap_compositeCentre B S hS hb Z₁ Y hY, Set.preimage_union,
    Set.preimage_union]

end AlgebraicGeometry.Space
end



