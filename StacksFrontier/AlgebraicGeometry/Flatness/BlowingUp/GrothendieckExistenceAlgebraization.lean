module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceProperSupport
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.UniversalFlatteningOfPure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.OpenImmersionAdicTransport
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Monomorphism
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension

/-!
# Algebraizing a compatible system from an open containing all the levels

In Situation [Stacks, Tag 0CTC], the proof of [Stacks, Tag 0CTK] produces, through
[Stacks, Tag 0CTD] to [Stacks, Tag 0CTI], an open `W ⊆ X` containing every `Xₙ` and a finitely
presented `𝒪_W`-module `ℱ` with support proper over `A` and with `ℱₙ = ℱ ⊗ 𝒪_{Xₙ}` compatibly with
the `φₙ`. It then concludes: `ℱ` is universally pure over `Spec A` ([Stacks, Tag 05K3]), so its
universal flattening `S' ⟶ Spec A` exists and is a monomorphism of finite presentation
([Stacks, Tag 05UG], [Stacks, Tag 05UH]); every `Spec Aₙ ⟶ Spec A` factors through it because
the base change of `ℱ` to `Spec Aₙ` is the flat module `ℱₙ`, so `S' = Spec A` by
[Stacks, Tag 0CTJ] and `ℱ` is flat; finally the pushforward of `ℱ` along `W ⊆ X` is supported on
the proper support of `ℱ` and has all the required properties. This file carries out that
conclusion.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.pullback_compatibility_of_adjoint`: compatibility of
  the isomorphisms `iₙ^* ℱ ≅ ℱₙ` with the `φₙ` follows from compatibility of their adjoints
  `ℱ ⟶ iₙ,* ℱₙ` with the transition maps of the pushed-forward system.
* `AlgebraicGeometry.GrothendieckExistence.isFinitePresentation_pushforward_ι_of_supp_subset`:
  the pushforward along the inclusion of an open of a module of finite presentation whose support
  lies in a closed subset of the ambient scheme contained in that open is of finite presentation.
* `ExistenceSituation.exists_pullback_iso_pushforward_of_isIso_adjoint`: the pushforward from the
  open carries isomorphisms with the levels, compatible with the `φₙ`.
* `ExistenceSituation.isFlatOver_of_forall_pullback_iso`: a module with proper support whose
  pullback to every level is isomorphic to `ℱₙ` is flat over `Spec A`.
* `ExistenceSituation.exists_algebraization_of_open`: the
  conclusion of the proof of [Stacks, Tag 0CTK], from an open and a module with proper support.
* `ExistenceSituation.exists_algebraization_of_isIso_adjoint`:
  the same, from an open and a module whose support is not yet known to be proper, by first
  shrinking the open as in [Stacks, Tag 0CTI].

## Implementation notes

The module on `W` is given as the restriction `G|_W` of an `𝒪_X`-module `G`, together with maps
`dₙ : G ⟶ iₙ,* ℱₙ` compatible with the transition maps
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.pushforwardTransition` and whose
adjoints `iₙ^* G ⟶ ℱₙ` are isomorphisms. This is the shape in which the proof of
[Stacks, Tag 0CTH] provides it, with `G = H⁰(K)` and `dₙ` the maps induced by `K ⟶ iₙ,* ℱₙ`.
The algebraization is `(W ⟶ X)_* (G|_W)`, and the maps `dₙ` factor uniquely through the unit
`G ⟶ (W ⟶ X)_* (G|_W)` because the targets `iₙ,* ℱₙ` are themselves pushed forward from `W`.

As in Situation [Stacks, Tag 0CTC], the index `n : ℕ` stands for the level `n + 1` of the
source.

## References

* [Stacks Project, Tag 0CTK](https://stacks.math.columbia.edu/tag/0CTK)
* [Stacks Project, Tag 05K3](https://stacks.math.columbia.edu/tag/05K3)
* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
* [Stacks Project, Tag 05UH](https://stacks.math.columbia.edu/tag/05UH)
* [Stacks Project, Tag 0CTJ](https://stacks.math.columbia.edu/tag/0CTJ)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.GrothendieckExistence

section Compatibility

variable {X X' X'' : Scheme.{u}} (t : X' ⟶ X'') (i' : X'' ⟶ X) (i : X' ⟶ X) (h : t ≫ i' = i)
  (F : X.Modules) {F' : X'.Modules} {F'' : X''.Modules}

/-- The map `i'_* F'' ⟶ i_* F'` induced by an isomorphism `φ : t^* F'' ≅ F'` along a
factorization `t ≫ i' = i`: the adjoint `F'' ⟶ t_* F'` of `φ`, pushed forward along `i'`. For the
inclusions of consecutive levels of Situation [Stacks, Tag 0CTC] this is
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.pushforwardTransition`. -/
def pushforwardTransitionOf (φ : (Scheme.Modules.pullback t).obj F'' ≅ F') :
    (Scheme.Modules.pushforward i').obj F'' ⟶ (Scheme.Modules.pushforward i).obj F' :=
  (Scheme.Modules.pushforward i').map
      ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F'' ≫
        (Scheme.Modules.pushforward t).map φ.hom) ≫
    (Scheme.Modules.pushforwardComp t i').hom.app F' ≫
    (Scheme.Modules.pushforwardCongr h).hom.app F'

/-- **Compatibility in pullback form from compatibility in pushforward form.** Let
`e'' : i'^* F ≅ F''` and `e' : i^* F ≅ F'` be isomorphisms whose adjoints `F ⟶ i'_* F''` and
`F ⟶ i_* F'` are compatible with the map `i'_* F'' ⟶ i_* F'` induced by `φ : t^* F'' ≅ F'`. Then
`e'` is `φ ∘ t^* e''` under the identification `t^* i'^* F ≅ i^* F`. -/
theorem pullback_compatibility_of_adjoint (φ : (Scheme.Modules.pullback t).obj F'' ≅ F')
    (e'' : (Scheme.Modules.pullback i').obj F ≅ F'') (e' : (Scheme.Modules.pullback i).obj F ≅ F')
    (hc : (Scheme.Modules.pullbackPushforwardAdjunction i').homEquiv _ _ e''.hom ≫
        pushforwardTransitionOf t i' i h φ =
      (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ e'.hom) :
    (Scheme.Modules.pullbackComp t i').app F ≪≫ (Scheme.Modules.pullbackCongr h).app F ≪≫ e' =
      (Scheme.Modules.pullback t).mapIso e'' ≪≫ φ := by
  subst h
  ext : 1
  dsimp [Scheme.Modules.pullbackCongr]
  rw [Category.id_comp]
  let adj₁ := (Scheme.Modules.pullbackPushforwardAdjunction i').comp
    (Scheme.Modules.pullbackPushforwardAdjunction t)
  let adj₂ := Scheme.Modules.pullbackPushforwardAdjunction (t ≫ i')
  have : Epi ((Scheme.Modules.pullbackComp t i').inv.app F) :=
    inferInstanceAs (Epi ((Scheme.Modules.pullbackComp t i').app F).inv)
  rw [← cancel_epi ((Scheme.Modules.pullbackComp t i').inv.app F), ← Category.assoc,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]
  apply (adj₂.homEquiv _ _).injective
  rw [← hc]
  have hu := unit_conjugateEquiv adj₁ adj₂ (Scheme.Modules.pullbackComp t i').inv F
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv t i'] at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, pushforwardTransitionOf]
  have hcongr : (Scheme.Modules.pushforwardCongr (rfl : t ≫ i' = t ≫ i')).hom.app F' = 𝟙 _ := by
    ext U : 1
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [hcongr, Category.comp_id, ← Category.assoc (adj₂.unit.app F), ← hu]
  have hnat₁ := (Scheme.Modules.pushforwardComp t i').hom.naturality
    ((Scheme.Modules.pullback t).map e''.hom)
  have hnat₂ := (Scheme.Modules.pushforwardComp t i').hom.naturality φ.hom
  simp only [Functor.comp_map] at hnat₁ hnat₂
  simp only [Category.assoc, Functor.comp_obj]
  rw [← reassoc_of% hnat₁, ← hnat₂]
  simp only [adj₁, Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  have := (Scheme.Modules.pullbackPushforwardAdjunction t).unit.naturality e''.hom
  simp only [Functor.id_map, Functor.comp_map] at this
  rw [reassoc_of% this]

end Compatibility

section General

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [IsIso adj.counit]

omit [IsIso adj.counit] in
/-- For an adjunction with invertible counit, every map into an object of the essential image of
the right adjoint factors through the unit. -/
private theorem exists_unit_comp_eq {G T : C} {M : D} (eT : T ≅ R.obj M) (d : G ⟶ T) :
    ∃ d' : R.obj (L.obj G) ⟶ T, adj.unit.app G ≫ d' = d :=
  ⟨R.map ((adj.homEquiv _ _).symm (d ≫ eT.hom)) ≫ eT.inv, by
    have := (adj.homEquiv _ _).apply_symm_apply (d ≫ eT.hom)
    rw [Adjunction.homEquiv_unit] at this
    rw [reassoc_of% this]
    simp⟩

/-- For an adjunction with invertible counit, maps out of `R (L G)` into an object of the
essential image of the right adjoint are determined by their composite with the unit. -/
private theorem unit_comp_cancel {G T : C} {M : D} (eT : T ≅ R.obj M)
    {a b : R.obj (L.obj G) ⟶ T} (h : adj.unit.app G ≫ a = adj.unit.app G ≫ b) : a = b := by
  have hR := adj.fullyFaithfulROfIsIsoCounit
  rw [← cancel_mono eT.hom, ← hR.map_preimage (a ≫ eT.hom), ← hR.map_preimage (b ≫ eT.hom)]
  congr 1
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hR.map_preimage, hR.map_preimage,
    reassoc_of% h]

/-- For an adjunction with invertible counit, the left adjoint inverts the unit. -/
private theorem isIso_map_unit (G : C) : IsIso (L.map (adj.unit.app G)) :=
  isIso_of_comp_hom_eq_id (adj.counit.app (L.obj G)) (adj.left_triangle_components G)

end General

section ModulePullback

/-- The pullback of modules along a morphism of schemes agrees with the pullback of modules along
the underlying morphism of sheaved spaces, by uniqueness of left adjoints. -/
def modulePullbackIsoPullback {Y Y' : Scheme.{u}} (f : Y ⟶ Y') :
    RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ≅ Scheme.Modules.pullback f :=
  Adjunction.leftAdjointUniq
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- **Flatness from flatness after base change along the identity.** A module whose base change
along the identity of the base is flat over the base is itself flat over the base. -/
theorem _root_.AlgebraicGeometry.FlatnessSituation.isFlatOver_of_isFlatAfterBaseChange_id
    (D : FlatnessSituation.{u}) (hid : D.IsFlatAfterBaseChange (Over.mk (𝟙 D.S))) :
    IsFlatOver D.f.toLRSHom.toShHom D.F := by
  let p₁ := pullback.fst D.f (𝟙 D.S)
  have hsq : IsPullback (inv p₁) D.f (pullback.snd D.f (𝟙 D.S)) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]
  have : ((RingedSpaceModuleAdjunction.modulePullback p₁.toLRSHom.toShHom).obj
      D.F).IsQuasicoherent :=
    SheafOfModules.modulePullback_isQuasicoherent p₁.toLRSHom.toShHom D.F
  let e₀ : (RingedSpaceModuleAdjunction.modulePullback (inv p₁).toLRSHom.toShHom).obj
      ((RingedSpaceModuleAdjunction.modulePullback p₁.toLRSHom.toShHom).obj D.F) ≅ D.F :=
    (modulePullbackIsoPullback (inv p₁)).app _ ≪≫
      (Scheme.Modules.pullback (inv p₁)).mapIso ((modulePullbackIsoPullback p₁).app D.F) ≪≫
      (Scheme.Modules.pullbackComp (inv p₁) p₁).app D.F ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p₁)).app D.F ≪≫
      (Scheme.Modules.pullbackId _).app D.F
  exact isFlatOver_of_moduleIso _ e₀ (modulePullback_isFlatOver hsq _ hid)

end ModulePullback

section OpenPushforward

variable {X : Scheme.{u}} (W : X.Opens)

/-- **Finite presentation of the pushforward along an open, away from the support.** Let
`N` be a module of finite presentation on an open `W` of `X` whose support lies, in `X`, in a
closed subset `T` contained in `W`. Then the pushforward of `N` to `X` is of finite presentation:
on `W` it restricts to `N`, and on the complement of `T` it vanishes. -/
theorem isFinitePresentation_pushforward_ι_of_supp_subset (N : W.toScheme.Modules)
    [N.IsFinitePresentation] (T : Set X) (hT : IsClosed T) (hTW : T ⊆ W)
    (hN : W.ι.base '' SheafOfModules.supp N ⊆ T) :
    ((Scheme.Modules.pushforward W.ι).obj N).IsFinitePresentation := by
  let M := (Scheme.Modules.pushforward W.ι).obj N
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let U : Bool → X.Opens := fun b => if b then V else W
  have hU : IsOpenCover U := top_unique fun x _ => by
    by_cases hx : x ∈ T
    exacts [Opens.mem_iSup.2 ⟨false, hTW hx⟩, Opens.mem_iSup.2 ⟨true, hx⟩]
  have hfp : ∀ b, (M.restrict (U b).ι).IsFinitePresentation := by
    rintro (_ | _)
    · exact (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
        ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app N).symm ‹_›
    · exact isFinitePresentation_of_isZero _
        (Stacks.Algebraization.isZero_restrictFunctor_pushforward_of_supp_subset W T N hN V
          fun _ hx => hx)
  have : M.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_restrict M U hU fun b =>
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (hfp b)).1
  exact isFinitePresentation_of_isOpenCover M U hU hfp

end OpenPushforward

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- The transition maps of the pushed-forward system are the maps induced by the `φₙ`. -/
theorem pushforwardTransition_eq (n : ℕ) :
    S.pushforwardTransition n = pushforwardTransitionOf (S.transitionScheme n)
      (S.closedImmersion (n + 1)) (S.closedImmersion n) (S.transition_fst n) (S.φ n) :=
  rfl

/-- **The isomorphisms with the levels for the pushforward from an open.** In Situation
[Stacks, Tag 0CTC], let `W ⊆ X` be an open containing every `Xₙ` and let `G` be an `𝒪_X`-module
with maps `dₙ : G ⟶ iₙ,* ℱₙ`, compatible with the transition maps of the system `(iₙ,* ℱₙ)` and
with invertible adjoints `iₙ^* G ⟶ ℱₙ`. Then the pushforward `(W ⟶ X)_* (G|_W)` carries
isomorphisms `iₙ^* ((W ⟶ X)_* (G|_W)) ≅ ℱₙ` compatible with the `φₙ`: each `dₙ` factors uniquely
through the unit `G ⟶ (W ⟶ X)_* (G|_W)` because `iₙ,* ℱₙ` is itself pushed forward from `W`. -/
theorem exists_pullback_iso_pushforward_of_isIso_adjoint (W : S.X.left.Opens)
    (hW : ∀ n, Set.range (S.closedImmersion n) ⊆ W) (G : S.X.left.Modules)
    (d : ∀ n, G ⟶ (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n))
    (hd : ∀ n, d (n + 1) ≫ S.pushforwardTransition n = d n)
    (hiso : ∀ n, IsIso
      (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
        (d n))) :
    ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj
        ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι)) ≅ S.F n,
      ∀ n : ℕ,
        (Scheme.Modules.pullbackComp (S.transitionScheme n)
              (S.closedImmersion (n + 1))).app
            ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι)) ≪≫
          (Scheme.Modules.pullbackCongr (S.transition_fst n)).app
            ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι)) ≪≫ e n =
        (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n := by
  let i := S.closedImmersion
  let lift : ∀ n, schemeAt S.system S.X n ⟶ W.toScheme := fun n =>
    IsOpenImmersion.lift W.ι (i n) (by rw [Scheme.Opens.range_ι]; exact hW n)
  have hlift : ∀ n, lift n ≫ W.ι = i n := fun n => IsOpenImmersion.lift_fac _ _ _
  let adjW := Scheme.Modules.restrictAdjunction W.ι
  let F := (Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι)
  let u : G ⟶ F := adjW.unit.app G
  let eT : ∀ n, (Scheme.Modules.pushforward (i n)).obj (S.F n) ≅
      (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pushforward (lift n)).obj (S.F n)) :=
    fun n => ((Scheme.Modules.pushforwardCongr (hlift n)).app _).symm ≪≫
      ((Scheme.Modules.pushforwardComp (lift n) W.ι).app _).symm
  choose d' hd' using fun n => exists_unit_comp_eq adjW (eT n) (d n)
  have hd'c : ∀ n, d' (n + 1) ≫ S.pushforwardTransition n = d' n := fun n =>
    unit_comp_cancel adjW (eT n) (by rw [reassoc_of% hd' (n + 1), hd' n, hd n])
  let adj := fun n => Scheme.Modules.pullbackPushforwardAdjunction (i n)
  have hpu : ∀ n, IsIso ((Scheme.Modules.pullback (i n)).map u) := fun n => by
    have h₁ : IsIso ((Scheme.Modules.pullback W.ι).map u) :=
      (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι) u).1
        (isIso_map_unit adjW G)
    have h₂ : IsIso ((Scheme.Modules.pullback W.ι ⋙ Scheme.Modules.pullback (lift n)).map u) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr (hlift n)) u).1
      ((NatIso.isIso_map_iff (Scheme.Modules.pullbackComp (lift n) W.ι) u).1 h₂)
  have hiso' : ∀ n, IsIso (((adj n).homEquiv _ _).symm (d' n)) := fun n => by
    have h := hiso n
    rw [← hd' n, Adjunction.homEquiv_naturality_left_symm] at h
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (hpu n) h
  let e : ∀ n, (Scheme.Modules.pullback (i n)).obj F ≅ S.F n := fun n =>
    asIso (((adj n).homEquiv _ _).symm (d' n))
  refine ⟨e, fun n => pullback_compatibility_of_adjoint _ _ _ (S.transition_fst n) F (S.φ n)
    (e (n + 1)) (e n) ?_⟩
  simp only [e, adj, i, asIso_hom, Equiv.apply_symm_apply]
  exact hd'c n

/-- The structure morphism of the scheme of an existence situation is separated, quasi-compact
and quasi-separated. -/
private theorem isSeparated_and_quasiCompact_and_quasiSeparated :
    IsSeparated S.X.hom ∧ QuasiCompact S.X.hom ∧ QuasiSeparated S.X.hom :=
  ⟨S.separated, S.finitePresentation.2.1, S.finitePresentation.2.2⟩

/-- **Flatness from flatness on the levels, [Stacks, Tag 0CTJ].** In Situation
[Stacks, Tag 0CTC], a quasi-coherent `𝒪_X`-module `ℱ` whose support is proper over `Spec A` and
whose pullback to each level `Xₙ` is isomorphic to `ℱₙ` is flat over `Spec A`: it is universally
pure ([Stacks, Tag 05K3]), so its universal flattening is a monomorphism of finite presentation
([Stacks, Tag 05UG], [Stacks, Tag 05UH]) through which every `Spec Aₙ ⟶ Spec A` factors, hence an
isomorphism by [Stacks, Tag 0CTJ]. -/
theorem isFlatOver_of_forall_pullback_iso (F : S.X.left.Modules) [hFqc : F.IsQuasicoherent]
    [F.IsFiniteType] [F.IsFinitePresentation]
    (hFprop : IsProperOver S.X.hom ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩)
    (e : ∀ n, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n) :
    IsFlatOver S.X.hom.toLRSHom.toShHom F := by
  obtain ⟨_, _, _⟩ := S.isSeparated_and_quasiCompact_and_quasiSeparated
  let D : FlatnessSituation.{u} :=
    { S := limitBase S.system, X := S.X.left, f := S.X.hom, F := F, isQuasicoherent := hFqc }
  have hpure : IsPureRelative S.X.hom F :=
    isPureRelative_of_isUniversallyPureRelative S.X.hom F
      (isUniversallyPureRelative_of_support_isProperOver S.X.hom F hFprop)
  obtain ⟨Zf, hmono, hfpZ, ⟨rep⟩⟩ :=
    exists_mono_finitePresentation_representableBy_of_isPureRelative S.X.hom F hpure
  have hlevel : ∀ n, D.IsFlatAfterBaseChange (Over.mk (baseProjection S.system n)) := fun n =>
    isFlatOver_of_moduleIso _
      ((modulePullbackIsoPullback (S.closedImmersion n)).app F ≪≫ e n).symm (S.flat n)
  have hfac : ∀ n, ∃ g : Spec (S.system.obj (op n)) ⟶ Zf.left,
      g ≫ Zf.hom = Spec.map ((limit.cone S.system).π.app (op n)) :=
    fun n => ⟨_, Over.w (rep.homEquiv.symm ⟨hlevel n⟩)⟩
  have hF' : ∀ n : ℕ, Function.Surjective (S.system.map (homOfLE (Nat.le_succ n)).op).hom ∧
      RingHom.ker (S.system.map (homOfLE (Nat.le_succ n)).op).hom ≤
        nilradical (S.system.obj (op (n + 1))) := fun n =>
    ⟨S.transition_surjective n,
      fun x hx => mem_nilradical.2 (S.transition_locallyNilpotent n x hx)⟩
  have : Mono Zf.hom := hmono
  have : LocallyOfFinitePresentation Zf.hom := hfpZ.1
  have : IsIso Zf.hom := isIso_of_forall_spec_factors_of_isLimit S.system (limit.cone S.system)
    (limit.isLimit _) hF' Zf.hom hfac
  let g : Over.mk (𝟙 (limitBase S.system)) ⟶ Zf := Over.homMk (inv Zf.hom) (by simp)
  exact D.isFlatOver_of_isFlatAfterBaseChange_id (rep.homEquiv g).down

/-- **The conclusion of the proof of [Stacks, Tag 0CTK].** In Situation [Stacks, Tag 0CTC], let
`W ⊆ X` be an open containing every `Xₙ` and let `G` be an `𝒪_X`-module with maps
`dₙ : G ⟶ iₙ,* ℱₙ`, compatible with the transition maps of the system `(iₙ,* ℱₙ)` and with
invertible adjoints `iₙ^* G ⟶ ℱₙ`, such that `G|_W` is of finite presentation with support `Z`
proper over `Spec A`. Then there is a finitely presented `𝒪_X`-module `ℱ`, flat over `Spec A`,
with support proper over `Spec A`, and with isomorphisms `iₙ^* ℱ ≅ ℱₙ` compatible with the
`φₙ`. -/
theorem exists_algebraization_of_open (W : S.X.left.Opens)
    (hW : ∀ n, Set.range (S.closedImmersion n) ⊆ W) (G : S.X.left.Modules)
    (d : ∀ n, G ⟶ (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n))
    (hd : ∀ n, d (n + 1) ≫ S.pushforwardTransition n = d n)
    (hiso : ∀ n, IsIso
      (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
        (d n)))
    [hfp : (G.restrict W.ι).IsFinitePresentation] (Z : Closeds W.toScheme)
    (hZ : (Z : Set W.toScheme) = SheafOfModules.supp (G.restrict W.ι))
    (hprop : IsProperOver (W.ι ≫ S.X.hom) Z) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n := by
  obtain ⟨_, _, _⟩ := S.isSeparated_and_quasiCompact_and_quasiSeparated
  let G' := G.restrict W.ι
  let F := (Scheme.Modules.pushforward W.ι).obj G'
  let Z' : Closeds S.X.left :=
    ⟨_, isClosed_image_of_isProperOver (W.ι ≫ S.X.hom) S.X.hom W.ι rfl Z hprop⟩
  have hZ'p : IsProperOver S.X.hom Z' :=
    isProperOver_image (W.ι ≫ S.X.hom) S.X.hom W.ι rfl Z hprop
  have hZ'W : (Z' : Set S.X.left) ⊆ W := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsuppG : W.ι.base '' SheafOfModules.supp G' ⊆ Z' := by
    rw [← hZ]
    exact subset_rfl
  have hFfp : F.IsFinitePresentation :=
    isFinitePresentation_pushforward_ι_of_supp_subset W G' Z' Z'.2 hZ'W hsuppG
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation F
      hFfp
  have hFprop : IsProperOver S.X.hom ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩ :=
    isProperOver_of_le S.X.hom
      (Stacks.Algebraization.supp_pushforward_subset_of_isClosed W Z' Z'.2 G' hsuppG) hZ'p
  obtain ⟨e, he⟩ := S.exists_pullback_iso_pushforward_of_isIso_adjoint W hW G d hd hiso
  exact ⟨F, hFfp, S.isFlatOver_of_forall_pullback_iso F hFprop e,
    ⟨⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩, rfl, hFprop⟩, e, he⟩

/-- **[Stacks, Tag 0CTI] followed by the conclusion of the proof of [Stacks, Tag 0CTK].** The
statement of `ExistenceSituation.exists_algebraization_of_open`
without the hypothesis on the support: the open `W` is first shrunk, by
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.exists_le_isProperOver_supp`, until
the support of `G|_W` is proper over `Spec A`. -/
theorem exists_algebraization_of_isIso_adjoint (W : S.X.left.Opens)
    (hW : ∀ n, Set.range (S.closedImmersion n) ⊆ W) (G : S.X.left.Modules)
    (d : ∀ n, G ⟶ (Scheme.Modules.pushforward (S.closedImmersion n)).obj (S.F n))
    (hd : ∀ n, d (n + 1) ≫ S.pushforwardTransition n = d n)
    (hiso : ∀ n, IsIso
      (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
        (d n)))
    [hfp : (G.restrict W.ι).IsFinitePresentation] :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n := by
  have := hiso 0
  obtain ⟨W', -, hW', hfp', Z, hZ, hZp⟩ := S.exists_le_isProperOver_supp W hW G
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion 0)).homEquiv _ _).symm
      (d 0)))
  exact S.exists_algebraization_of_open W' hW' G d hd hiso Z hZ hZp

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
