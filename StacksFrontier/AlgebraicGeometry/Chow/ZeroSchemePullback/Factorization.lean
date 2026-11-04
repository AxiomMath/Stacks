module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.Topology.OpensMapFinal
import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization

/-!
# Factorization through the zero scheme of a section

A morphism of schemes `f : Y ⟶ X` factors through the zero scheme `Z(s)` of a global section `s`
of an invertible module `L` on `X` precisely when the pulled-back section `f^* s` vanishes. This
is the universal property of `Z(s)` as the zero locus of `s`.

## Main results

* `Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme` — the pulled-back
  section vanishes if and only if the morphism factors through the zero scheme.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Divisors

/-- Trivializing affine opens of an invertible module are cofinal: every point of every open has
a trivializing affine neighbourhood inside that open. -/
private theorem exists_affine_frame_subset (X : Scheme.{u}) (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) (V : X.Opens) (hx : x ∈ V) :
    ∃ (U : X.affineOpens)
      (_eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)),
      x ∈ U.1 ∧ U.1 ≤ V := by
  classical
  have hfree :=
    (Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry
      (X := X.toRingedSpace) L).mp h
  obtain ⟨q, hq, hrank⟩ := hfree.exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]
    simp
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨i, hxi⟩ := hxcover
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWmeet⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx, hxi⟩ : x ∈ V ⊓ q.X i)
      (V ⊓ q.X i).isOpen
  let U : X.affineOpens := ⟨W, hW⟩
  have hWsubset : (U : X.Opens) ≤ V ⊓ q.X i := fun _ hy => hWmeet hy
  have : IsIso (q.generators i).π := hq.isIso i
  let eIndex : (q.generators i).I ≃ PUnit.{u + 1} :=
    (hrank i).some.trans (Equiv.equivPUnit _)
  let eV : L.over (q.X i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (q.X i)) :=
    (asIso (q.generators i).π).symm ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso eIndex.toIso ≪≫
      Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over (q.X i)))
  let g : (U : X.Opens) ⟶ q.X i := homOfLE (hWsubset.trans inf_le_right)
  exact ⟨U, ((SheafOfModules.overFunctorMap X.ringCatSheaf g).app L).symm ≪≫
      (SheafOfModules.overMap X.ringCatSheaf g).mapIso eV ≪≫
      SheafOfModules.overMapUnitIso g, hxW, hWsubset.trans inf_le_left⟩

/-- The preimage functor on opens along a morphism of schemes is final: the whole space is a
terminal object of each of its structured-arrow categories. -/
private theorem opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  Stacks.Topology.final_opensMap f.base

/-- A trivialization of a sheaf of modules over an open, transported from the category of
modules over the restricted structure sheaf to the category of modules on the open subscheme. -/
private def frameIsoOnOpen (X : Scheme.{u}) (L : X.Modules) {U : X.affineOpens}
    (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    L.restrict U.1.ι ≅ SheafOfModules.unit ((U.1).toScheme.ringCatSheaf) :=
  let α := Scheme.Modules.overFunctorEquiv (X := X) U.1
  (α.app L).symm ≪≫ (Scheme.Modules.overEquiv U.1).functor.mapIso eU ≪≫
    (α.app (SheafOfModules.unit X.ringCatSheaf) ≪≫ Scheme.Modules.restrictUnitIso U.1.ι)

/-- Naturality of the unit of the pullback--pushforward adjunction, read on a global section. -/
public theorem pullbackGlobalSections_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ (⊤ : Y.Opens))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app ⊤ (φ.app ⊤ s) :=
  ((CategoryTheory.comp_apply _ _ s).symm.trans
      (congrArg (fun ψ => ψ s)
        (congrArg (fun η => Scheme.Modules.Hom.app η ⊤)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality φ)))).trans
    (CategoryTheory.comp_apply _ _ s)

/-- The comparison map `f^* 𝒪_Y ⟶ 𝒪_X` carries the pullback of a function `s` on `Y` to its
pullback `f^# s` in the ordinary sense. -/
public theorem pullbackGlobalSections_unit_appTop {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Γ(Y, ⊤))
    [(SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint]
    [(TopologicalSpace.Opens.map f.base).Final] :
    ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app (Opposite.op ⊤))
        (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) s) =
      f.app (⊤ : Y.Opens) s := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom
  let η := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have hη := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [adj.homEquiv_unit] at hη
  have h' := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)) s) hη
  change ((((adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)).val.app (Opposite.op ⊤)) ≫
      (((SheafOfModules.pushforward f.toRingCatSheafHom).map η).val.app
        (Opposite.op ⊤))) s) = _ at h'
  change (((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map η.val).app
      (Opposite.op ⊤)).hom
      ((((adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)).val.app
        (Opposite.op ⊤)).hom) s) =
    (((SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app
      (Opposite.op ⊤)).hom) s at h'
  change ((η.val.app (Opposite.op ((TopologicalSpace.Opens.map f.base).obj
      (⊤ : Y.Opens)))).hom
        ((((adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)).val.app
          (Opposite.op ⊤)).hom) s)) = f.app (⊤ : Y.Opens) s at h'
  have hbridge : (η.val.app (Opposite.op ⊤))
        (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) s) =
      (η.val.app (Opposite.op ⊤))
        (((adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)).val.app (Opposite.op ⊤)) s) :=
    congrArg (fun z => (η.val.app (Opposite.op ⊤)) z)
      (ConcreteCategory.congr_hom
        (pullbackGlobalSections_eq_unit f (SheafOfModules.unit Y.ringCatSheaf)) s)
  refine hbridge.trans ?_
  convert h' using 1
  simp [adj, η, ModuleCat.Hom.hom, ConcreteCategory.hom]
  rfl

/-- For a trivialized module, the comparison map `f^* 𝒪_Y ⟶ 𝒪_X` carries the pullback of a
section to the pullback of the function representing it. -/
public theorem pullbackGlobalSections_frame_appTop {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(M, ⊤))
    [(SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint]
    [(TopologicalSpace.Opens.map f.base).Final] :
    ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app
          (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens))))
        (((Scheme.Modules.pullback f).map e.hom).app (f ⁻¹ᵁ (⊤ : Y.Opens))
          (pullbackGlobalSections f M s)) =
      f.app (⊤ : Y.Opens) (e.hom.app ⊤ s) := by
  have hu' : ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app
        (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens))))
        (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) (e.hom.app ⊤ s)) =
      f.app (⊤ : Y.Opens) (e.hom.app ⊤ s) :=
    pullbackGlobalSections_unit_appTop f (e.hom.app ⊤ s)
  have hA : pullbackGlobalSections f M s =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ s :=
    ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit f M) s
  have hB : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit Y.ringCatSheaf)).app ⊤ (e.hom.app ⊤ s) =
      pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) (e.hom.app ⊤ s) :=
    (ConcreteCategory.congr_hom
      (pullbackGlobalSections_eq_unit f (SheafOfModules.unit Y.ringCatSheaf)) _).symm
  refine Eq.trans (congrArg (fun z =>
    ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app
        (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens))))
      (((Scheme.Modules.pullback f).map e.hom).app (f ⁻¹ᵁ (⊤ : Y.Opens)) z)) hA) ?_
  refine Eq.trans (congrArg (fun z =>
    ((SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app
        (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens)))) z)
    ((pullbackGlobalSections_naturality f e.hom s).trans hB)) hu'

/-- An isomorphism of sheaves of modules detects vanishing of sections. -/
private theorem hom_app_eq_zero_iff {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [IsIso φ] (U : X.Opens) (s : Γ(M, U)) : φ.app U s = 0 ↔ s = 0 :=
  map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (φ.app U)).injective

/-- For a trivialized module, the pulled-back section vanishes exactly when the pullback of the
function representing it vanishes. -/
private theorem pullbackGlobalSections_eq_zero_iff_frame_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(M, ⊤))
    [(SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint]
    [(TopologicalSpace.Opens.map f.base).Final]
    [IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)] :
    pullbackGlobalSections f M s = 0 ↔ f.app (⊤ : Y.Opens) (e.hom.app ⊤ s) = 0 := by
  have h := pullbackGlobalSections_frame_appTop f M e s
  have : IsIso e.hom := e.isIso_hom
  have : IsIso ((Scheme.Modules.pullback f).map e.hom) :=
    Functor.map_isIso (Scheme.Modules.pullback f) e.hom
  have hα := hom_app_eq_zero_iff ((Scheme.Modules.pullback f).map e.hom)
    (f ⁻¹ᵁ (⊤ : Y.Opens))
  let η := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let β := η.val.app (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens)))
  have : IsIso η.val := Functor.map_isIso (SheafOfModules.forget _) η
  have : IsIso β := Functor.map_isIso
    (PresheafOfModules.evaluation X.ringCatSheaf.obj
      (Opposite.op (f ⁻¹ᵁ (⊤ : Y.Opens)))) η.val
  have hβ : ∀ y, (ConcreteCategory.hom β) y = 0 ↔ y = 0 := fun _ =>
    map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso β).injective
  exact ⟨fun hs => h.symm.trans ((hβ _).mpr ((hα _).mpr hs)),
    fun hs => (hα _).mp ((hβ _).mp (h.trans hs))⟩

/-- For an open immersion, the pullback map on global sections is restriction to the image,
read through the comparison of the restriction functor with the pullback functor. -/
private theorem pullbackGlobalSections_open
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i] (L : X.Modules) (s : Γ(L, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app L).app ⊤
        ((L.presheaf.map (homOfLE le_top).op) s) = pullbackGlobalSections i L s := by
  have h := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction i) L
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h'
  exact h'.trans (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit i L) s).symm

/-- Along an open immersion, the pulled-back section vanishes exactly when the original section
restricts to zero on the image. -/
private theorem pullbackGlobalSections_open_eq_zero_iff
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i] (L : X.Modules) (s : Γ(L, ⊤)) :
    pullbackGlobalSections i L s = 0 ↔
      L.presheaf.map (homOfLE (show i ''ᵁ ⊤ ≤ ⊤ from le_top)).op s = 0 := by
  rw [← pullbackGlobalSections_open]
  exact hom_app_eq_zero_iff ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app L) ⊤ _

/-- Vanishing of a pulled-back section along a composite is vanishing of the twice-pulled-back
section. -/
private theorem pullbackGlobalSections_comp_eq_zero_iff
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (s : Γ(L, ⊤)) :
    pullbackGlobalSections (f ≫ g) L s = 0 ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
        (pullbackGlobalSections g L s) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  exact hom_app_eq_zero_iff ((Scheme.Modules.pullbackComp f g).hom.app L) ⊤ _

/-- Vanishing of a pulled-back section is invariant under an isomorphism of the module. -/
private theorem pullbackGlobalSections_hom_eq_zero_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N) [IsIso φ] (s : Γ(M, ⊤)) :
    pullbackGlobalSections f N (φ.app ⊤ s) = 0 ↔ pullbackGlobalSections f M s = 0 := by
  have h' : ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackGlobalSections f M s) =
      pullbackGlobalSections f N (φ.app ⊤ s) :=
    (congrArg (fun z => ((Scheme.Modules.pullback f).map φ).app ⊤ z)
        (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit f M) s)).trans
      ((pullbackGlobalSections_naturality f φ s).trans
        (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit f N) _).symm)
  rw [← h']
  exact hom_app_eq_zero_iff ((Scheme.Modules.pullback f).map φ) ⊤ _

/-- A trivialization of `L` over an open `U`, read on sections over `U` as a
`Γ(X, U)`-linear equivalence `Γ(L, U) ≃ₗ Γ(X, U)`. -/
private def restrictedFrameSections (X : Scheme.{u}) (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Γ(L, U.ι ''ᵁ ⊤) ≃ₗ[Γ(X, U.ι ''ᵁ ⊤)] Γ(X, U.ι ''ᵁ ⊤) := by
  have hiso : IsIso (Scheme.Modules.Hom.app (X := (U : Scheme)) e.hom ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp e.isIso_hom ⊤
  have hρ : (Scheme.Modules.restrictAppIso U.ι L ⊤).hom = 𝟙 _ := rfl
  have hρ' : ∀ y : Γ(L.restrict U.ι, ⊤),
      (ConcreteCategory.hom (Scheme.Modules.restrictAppIso U.ι L ⊤).hom) y = y := fun y =>
    (congrArg (fun m => (ConcreteCategory.hom m) y) hρ).trans (CategoryTheory.id_apply y)
  have hr : ∀ r : Γ(X, U.ι ''ᵁ ⊤),
      (Scheme.Hom.appIso U.ι (⊤ : (U : Scheme).Opens)).inv r = r := fun r => by
    rw [Scheme.Opens.ι_appIso]
    exact CategoryTheory.id_apply r
  refine LinearEquiv.ofBijective
    ({ toFun := fun x => e.hom.app ⊤ x
       map_add' := fun a b => map_add _ a b
       map_smul' := fun r x => ?_ } :
      Γ(L, U.ι ''ᵁ ⊤) →ₗ[Γ(X, U.ι ''ᵁ ⊤)] Γ(X, U.ι ''ᵁ ⊤))
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤))
  have h2 := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι L ⊤ r x
  have h3 := (congrArg (fun z : Γ(X, U.ι ''ᵁ ⊤) =>
      z • (ConcreteCategory.hom (Scheme.Modules.restrictAppIso U.ι L ⊤).hom) x) (hr r)).trans
    (congrArg (fun y : Γ(L, U.ι ''ᵁ ⊤) => r • y) (hρ' x))
  have hb := (hρ' _).symm.trans (h2.trans h3)
  exact (congrArg (fun z => (ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom ⊤)) z)
    hb.symm).trans (Scheme.Modules.Hom.app_smul e.hom r x)

/-- Over a trivializing open `U`, the pulled-back section vanishes on `f⁻¹(U)` exactly when the
pullback of the function representing `s` on `U` vanishes. -/
private theorem pullbackGlobalSections_local_frame_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE (show (f ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f L s) = 0 ↔
      f.app (U.ι ''ᵁ ⊤) (restrictedFrameSections X L U e
        (L.presheaf.map (homOfLE le_top).op s)) = 0 := by
  let g := f ∣_ U
  have hcomp : g ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  rw [← pullbackGlobalSections_open_eq_zero_iff,
    ← pullbackGlobalSections_comp_eq_zero_iff, ← hcomp,
    pullbackGlobalSections_comp_eq_zero_iff, ← pullbackGlobalSections_open U.ι L s]
  have : (TopologicalSpace.Opens.map g.base).Final := opensMap_final g
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal g.toRingCatSheafHom
  refine Iff.trans (pullbackGlobalSections_hom_eq_zero_iff g
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app L)
    (L.presheaf.map (homOfLE le_top).op s)) ?_
  refine Iff.trans (pullbackGlobalSections_eq_zero_iff_frame_appTop g (L.restrict U.ι) e
    (L.presheaf.map (homOfLE le_top).op s)) ?_
  show g.app ⊤ (e.hom.app ⊤ (L.presheaf.map (homOfLE le_top).op s)) = 0 ↔
    f.app (U.ι ''ᵁ ⊤) (e.hom.app ⊤ (L.presheaf.map (homOfLE le_top).op s)) = 0
  dsimp only [g]
  rw [morphismRestrict_app]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).injective

/-- Vanishing of the restriction of a section to an open depends only on that open. -/
private theorem restriction_eq_zero_congr {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hUV : U = V) (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0 ↔
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s = 0 := by
  subst V
  rfl

/-- Over a trivializing affine open `U`, the pulled-back section vanishes on `f⁻¹(U)` exactly
when the ideal of the zero scheme on `U` is carried to zero by `f`. -/
private theorem pullbackGlobalSections_local_ideal_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : X.affineOpens)
    (e : L.restrict U.1.ι ≅ SheafOfModules.unit U.1.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE (show f ⁻¹ᵁ U.1 ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f L s) = 0 ↔
      (_root_.Stacks.Divisors.zeroScheme X L s).ideal U ≤ RingHom.ker (f.app U.1).hom := by
  let W : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤, by rw [Scheme.Opens.ι_image_top]; exact U.2⟩
  have hW : W = U := Subtype.ext (by simp [W])
  have h := pullbackGlobalSections_local_frame_iff f L s U.1 e
  have heq := _root_.Stacks.Divisors.zeroScheme_ideal_of_trivialization X L s W
    (restrictedFrameSections X L U.1 e) _ rfl
  have hspan : (_root_.Stacks.Divisors.zeroScheme X L s).ideal W ≤
      RingHom.ker (f.app W.1).hom ↔
      f.app W.1 (restrictedFrameSections X L U.1 e
        (L.presheaf.map (homOfLE le_top).op s)) = 0 := by
    rw [heq, Ideal.span_le]
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  rw [← hspan, hW] at h
  exact (restriction_eq_zero_congr ((Scheme.Modules.pullback f).obj L)
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U.1)).symm (pullbackGlobalSections f L s)).trans h

/-- An ideal sheaf is contained in the kernel of a morphism as soon as that holds locally on the
source: the sections of the structure sheaf of the source glue. -/
private theorem ideal_le_ker_of_locally
    {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData)
    (h : ∀ (W : X.affineOpens) (x : X), x ∈ W.1 →
      ∃ U : X.affineOpens, x ∈ U.1 ∧ U ≤ W ∧
        I.ideal U ≤ RingHom.ker (f.app U.1).hom) : I ≤ f.ker := by
  classical
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro W a ha
  show f.app W.1 a = 0
  have hlocal (y : f ⁻¹ᵁ W.1) := h W (f y.1) y.2
  choose U hy hUW hker using hlocal
  let V (y : f ⁻¹ᵁ W.1) : Y.Opens := f ⁻¹ᵁ (U y).1
  have hV (y) : V y ≤ f ⁻¹ᵁ W.1 := fun z hz => hUW y hz
  have hcover : f ⁻¹ᵁ W.1 ≤ ⨆ y, V y := fun y hyW =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hyW⟩, hy ⟨y, hyW⟩⟩
  apply Y.sheaf.eq_of_locally_eq' V (f ⁻¹ᵁ W.1) (fun y => homOfLE (hV y)) hcover
  intro y
  have hz := hker y (I.ideal_le_comap_ideal (hUW y) ha)
  change f.app (U y).1 (X.presheaf.map (homOfLE (hUW y)).op a) = 0 at hz
  have hn := congrArg (fun φ => φ a) (f.naturality (homOfLE (hUW y)).op)
  show (Y.presheaf.map (homOfLE (hV y)).op) (f.app W.1 a) =
    (Y.presheaf.map (homOfLE (hV y)).op) 0
  rw [map_zero]
  refine Eq.trans ?_ hz
  exact ((CategoryTheory.comp_apply _ _ a).symm.trans
    (hn.trans (CategoryTheory.comp_apply _ _ a))).symm

/-- A global section `s` of an invertible module `L` on `X` vanishes after pullback along
`f : Y ⟶ X` if and only if `f` factors through the zero scheme of `s`. -/
@[stacks 02OR "factorization"]
theorem pullbackSection_eq_zero_iff_factorsThrough_zeroScheme
    (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackGlobalSections f L s = 0 ↔
      ∃ g : Y ⟶ (_root_.Stacks.Divisors.zeroScheme X L s).subscheme,
        g ≫ (_root_.Stacks.Divisors.zeroScheme X L s).subschemeι = f := by
  classical
  rw [_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker]
  constructor
  · intro hs
    apply ideal_le_ker_of_locally f (_root_.Stacks.Divisors.zeroScheme X L s)
    intro W x hx
    obtain ⟨U, eU, hxU, hUW⟩ := exists_affine_frame_subset X L x W.1 hx
    refine ⟨U, hxU, hUW, ?_⟩
    apply (pullbackGlobalSections_local_ideal_iff f L s U (frameIsoOnOpen X L eU)).mp
    simp [hs]
  · intro hI
    have hlocal (y : Y) := exists_affine_frame_subset X L (f y) ⊤ (by trivial)
    choose U eU hy _ using hlocal
    let V (y : Y) : Y.Opens := f ⁻¹ᵁ (U y).1
    let F : TopCat.Sheaf AddCommGrpCat Y :=
      ⟨((Scheme.Modules.pullback f).obj L).presheaf,
        ((Scheme.Modules.pullback f).obj L).isSheaf⟩
    have hcover : (⊤ : Y.Opens) ≤ ⨆ y, V y := fun y _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
    apply F.eq_of_locally_eq' V ⊤ (fun _ => homOfLE le_top) hcover
    intro y
    have hzero := (pullbackGlobalSections_local_ideal_iff f L s (U y)
      (frameIsoOnOpen X L (eU y))).mpr ((hI (U y)).trans (f.ideal_ker_le (U y)))
    simpa only [map_zero] using hzero

end Stacks.Divisors

end

end
