module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.SupportedSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ExactnessUnconditional

/-!
# The derived functors of the supported subsheaf

Let `U ⊆ X` be open, `j : U ⟶ X` its inclusion, and `𝒦_U` the subsheaf of sections supported in
`X ∖ U` (`AlgebraicGeometry.Scheme.supportedSubsheaf`). This file proves the two facts about the
sheaves `R^q 𝒦_U(𝓕)` which the dévissage of Exposé XVIII-A, Lemma 2.2 uses:

* their stalks vanish at geometric points over `U` (`𝒦_U` vanishes on `U`, and stalks are exact);
* for `q ≥ 1` the stalk of `R^q 𝒦_U(𝓕)` at a geometric point is a quotient of the stalk of
  `R^{q-1} j_*(𝓕|_U)` there: the sequence `0 → 𝒦_U(𝓕) → 𝓕 → j_* (𝓕|_U) → 0` is short exact at an
  injective `𝓕` (restriction of sections of an injective sheaf along the monomorphism
  `W ×_X U ⟶ W` is surjective, Stacks 093X), so its long exact sequence gives
  `R^{q-1}(j_* ∘ (-)|_U) ↠ R^q 𝒦_U`, and restriction to `U` is exact and preserves injectives.

## Main results

* `AlgebraicGeometry.Scheme.isZero_stalk_rightDerived_supportedSubsheaf_of_mem`
* `AlgebraicGeometry.Scheme.isZero_stalk_rightDerived_supportedSubsheaf_of_isZero`

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (U : X.Opens)

/-- Restriction to `U` is left adjoint to direct image along `j : U ⟶ X`, on sections. -/
abbrev complementAdj :
    Stacks.EtaleCohomology.etaleRestriction.{u, 0} U.ι ⊣
      Stacks.EtaleCohomology.smallEtalePushforwardAb U.ι :=
  (Etale.smallEtaleComposeBaseChangeAdj U.ι).sheafPushforwardContinuous
    (E := AddCommGrpCat.{u + 1}) (smallEtaleTopology U.toScheme) (smallEtaleTopology X)

/-- The unit of `complementAdj U` at `P`, on a section over `W`, is restriction along the
counit `W ×_X U ⟶ W`. -/
theorem complementAdj_unit_app_app (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (W : X.Etale) (t : P.obj.obj (op W)) :
    ((complementAdj U).unit.app P).hom.app (op W) t =
      P.obj.map ((Etale.smallEtaleComposeBaseChangeAdj U.ι).counit.app W).op t :=
  rfl

/-- The counit `W ×_X U ⟶ W` of composition with `j` and base change along `j`. -/
abbrev complementCounit (W : X.Etale) :
    (Etale.smallEtaleCompose U.ι).obj ((Stacks.EtaleCohomology.smallEtaleBaseChange U.ι).obj W) ⟶
      W :=
  (Etale.smallEtaleComposeBaseChangeAdj U.ι).counit.app W

/-- The underlying morphism of `complementCounit U W` is the first projection
`W ×_X U ⟶ W`. -/
theorem complementCounit_left (W : X.Etale) :
    (complementCounit U W).left = pullback.fst W.hom U.ι := rfl

/-- A section whose restriction to `W ×_X U` vanishes is supported in `X ∖ U`: every object over
`W` landing in `U` factors through `W ×_X U`. -/
theorem mem_supportedSubgroup_of_map_complementCounit_eq_zero
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {W : X.Etale} (t : P.obj.obj (op W))
    (ht : P.obj.map (complementCounit U W).op t = 0) : t ∈ supportedSubgroup U P W := by
  intro W' f hW'
  let g := hW'.some
  have hcond : f.left ≫ W.hom = g.left ≫ U.ι :=
    (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  let l : W' ⟶ (Etale.smallEtaleCompose U.ι).obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange U.ι).obj W) :=
    MorphismProperty.Over.homMk (pullback.lift f.left g.left hcond) (by
      have h1 : pullback.lift f.left g.left hcond ≫ pullback.snd W.hom U.ι = g.left :=
        pullback.lift_snd _ _ _
      have h2 : g.left ≫ U.ι = W'.hom := MorphismProperty.Over.w g
      change pullback.lift f.left g.left hcond ≫ pullback.snd W.hom U.ι ≫ U.ι = W'.hom
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.ι) h1).trans h2)) trivial
  have hl : l ≫ complementCounit U W = f := MorphismProperty.Over.Hom.ext (by
    change pullback.lift f.left g.left hcond ≫ pullback.fst W.hom U.ι = f.left
    exact pullback.lift_fst _ _ _)
  rw [← hl, op_comp, P.obj.map_comp, ConcreteCategory.comp_apply, ht, map_zero]

/-- The object `W ×_X U` lands in `U`. -/
theorem landsIn_complementCounit (W : X.Etale) :
    LandsIn U ((Etale.smallEtaleCompose U.ι).obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange U.ι).obj W)) := by
  refine ⟨homToOpensToEtale _ U ?_⟩
  rintro _ ⟨y, rfl⟩
  change U.ι (((Stacks.EtaleCohomology.smallEtaleBaseChange U.ι).obj W).hom y) ∈ U
  have := Set.mem_range_self (f := U.ι.base)
    (((Stacks.EtaleCohomology.smallEtaleBaseChange U.ι).obj W).hom y)
  rwa [Scheme.Opens.range_ι] at this

/-- The composite `𝒦_U(𝓕) ⟶ 𝓕 ⟶ j_*(𝓕|_U)` vanishes. -/
theorem supportedSubsheafι_comp_unit :
    supportedSubsheafι U ≫ (complementAdj U).unit = 0 := by
  ext P W s
  change P.obj.map (complementCounit U W.unop).op s.1 = 0
  exact s.2 _ _ (landsIn_complementCounit U W.unop)

/-- The short complex `𝒦_U(𝓕) ⟶ 𝓕 ⟶ j_*(𝓕|_U)`. -/
abbrev supportedShortComplex (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  NatTrans.appShortComplex (supportedSubsheafι U) (complementAdj U).unit
    (supportedSubsheafι_comp_unit U) P

/-- The sequence `0 ⟶ 𝒦_U(𝓕) ⟶ 𝓕 ⟶ j_*(𝓕|_U)` is exact: `𝒦_U(𝓕)` is the kernel. -/
theorem supportedShortComplex_exact (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (supportedShortComplex U P).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun {T} g hg => ⟨{
      app W := AddCommGrpCat.ofHom
        { toFun := fun t => ⟨g.hom.app W t,
            mem_supportedSubgroup_of_map_complementCounit_eq_zero U P _
              (congrArg (fun φ : T ⟶ _ => φ.hom.app W t) hg :)⟩
          map_zero' := by ext; exact map_zero _
          map_add' := fun _ _ => by ext; exact map_add _ _ _ }
      naturality _ _ f := by
        ext t
        exact Subtype.ext (NatTrans.naturality_apply g.hom f t) }⟩)
    (fun g hg => by ext; rfl) (fun g hg m hm => ?_))
  ext W t
  exact Subtype.ext <| congrArg (fun φ : _ ⟶ P => φ.hom.app W t) hm

/-- The counit `W ×_X U ⟶ W` is a monomorphism, since `U ⟶ X` is one. -/
instance mono_complementCounit (W : X.Etale) : Mono (complementCounit U W) := by
  apply Functor.mono_of_mono_map (Scheme.Etale.forget X ⋙ Over.forget X)
  change Mono (pullback.fst W.hom U.ι)
  infer_instance

/-- At an injective sheaf the restriction `𝓕 ⟶ j_*(𝓕|_U)` is an epimorphism (Stacks 093X). -/
theorem epi_complementAdj_unit_app_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    Epi ((complementAdj U).unit.app I) := by
  apply Functor.epi_of_epi_map (sheafToPresheaf _ _)
  have : ∀ W, Epi (((sheafToPresheaf _ _).map ((complementAdj U).unit.app I)).app W) := by
    intro W
    rw [AddCommGrpCat.epi_iff_surjective]
    exact Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective
      X.smallEtaleTopology I (complementCounit U W.unop)
  exact NatTrans.epi_of_epi_app _

/-- **The sequence `0 ⟶ 𝒦_U(𝓕) ⟶ 𝓕 ⟶ j_*(𝓕|_U) ⟶ 0` is short exact at an injective sheaf.** -/
theorem supportedShortComplex_shortExact_of_injective
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    (supportedShortComplex U I).ShortExact :=
  ShortComplex.ShortExact.mk' (supportedShortComplex_exact U I)
    (inferInstanceAs (Mono ((supportedSubsheafι U).app I)))
    (epi_complementAdj_unit_app_of_injective U I)

/-! ### Stalks of the derived functors -/

/-- A functor all of whose values vanish has vanishing right derived functors. -/
theorem isZero_rightDerived_obj_of_forall_isZero {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    [HasInjectiveResolutions 𝒜] (G : 𝒜 ⥤ AddCommGrpCat.{u + 1}) [G.Additive]
    (h : ∀ A, IsZero (G.obj A)) (F : 𝒜) (i : ℕ) : IsZero ((G.rightDerived i).obj F) :=
  (HomologicalComplex.ExactAt.isZero_homology
    (HomologicalComplex.ExactAt.of_isZero (h _))).of_iso
      ((injectiveResolution F).isoRightDerivedObj _ i)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The stalk of the supported subsheaf at a geometric point over `U` vanishes. -/
theorem isZero_stalk_supportedSubsheaf_of_mem (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : Spec (.of Ω) ⟶ X) (hs : s (IsLocalRing.closedPoint Ω) ∈ U) :
    IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s).obj ((supportedSubsheaf U).obj P)) := by
  have hrange : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hs
  let s' : Spec (.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι s hrange
  have hs' : s' ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hzero : IsZero ((Stacks.EtaleCohomology.smallEtalePullbackAb U.ι).obj
      ((supportedSubsheaf U).obj P)) :=
    (isZero_etaleRestriction_supportedSubsheaf U P).of_iso
      ((Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleRestriction U.ι).app _)
  have h := ((Stacks.EtaleCohomology.smallEtaleStalkAb s').map_isZero hzero).of_iso
    ((Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso U.ι s').app _).symm
  rwa [hs'] at h

/-- **The stalks of `R^q 𝒦_U(𝓕)` at geometric points over `U` vanish.** -/
theorem isZero_stalk_rightDerived_supportedSubsheaf_of_mem
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (s : Spec (.of Ω) ⟶ X) (hs : s (IsLocalRing.closedPoint Ω) ∈ U) :
    IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s).obj
      (((supportedSubsheaf U).rightDerived q).obj P)) :=
  (isZero_rightDerived_obj_of_forall_isZero _
    (fun A => isZero_stalk_supportedSubsheaf_of_mem U A s hs) P q).of_iso
    ((Functor.rightDerivedCompIso (supportedSubsheaf U)
      (Stacks.EtaleCohomology.smallEtaleStalkAb s) q).app P).symm

/-- **The stalk of `R^{n+1} 𝒦_U(𝓕)` is a quotient of that of `R^n j_*(𝓕|_U)`**: if the latter
vanishes at a geometric point, so does the former. -/
theorem isZero_stalk_rightDerived_supportedSubsheaf_succ
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (s : Spec (.of Ω) ⟶ X)
    (h : IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s).obj
      (((Stacks.EtaleCohomology.smallEtalePushforwardAb U.ι).rightDerived n).obj
        ((Stacks.EtaleCohomology.etaleRestriction.{u, 0} U.ι).obj P)))) :
    IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s).obj
      (((supportedSubsheaf U).rightDerived (n + 1)).obj P)) := by
  have hex := exact_rightDerived_composableArrows₅ (supportedSubsheafι U) (complementAdj U).unit
    (supportedSubsheafι_comp_unit U)
    (fun I hI => @supportedShortComplex_shortExact_of_injective X U I hI) (injectiveResolution P) n
  have hepi := (hex.exact 2).epi_f ((CategoryTheory.isZero_rightDerived_id_obj P n).eq_of_tgt _ _)
  have h0 : IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s).obj
      (((Stacks.EtaleCohomology.etaleRestriction.{u, 0} U.ι ⋙
        Stacks.EtaleCohomology.smallEtalePushforwardAb U.ι).rightDerived n).obj P)) :=
    h.of_iso ((Stacks.EtaleCohomology.smallEtaleStalkAb s).mapIso
      (Functor.rightDerivedCompIsoOfPreservesInjectiveObjects _ _ P n))
  exact @IsZero.of_epi _ _ _ _ _ ((Stacks.EtaleCohomology.smallEtaleStalkAb s).map _)
    (@Functor.map_epi _ _ _ _ _ _ _ _ _ hepi) h0

end AlgebraicGeometry.Scheme

end
