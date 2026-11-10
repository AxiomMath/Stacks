module

public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit

/-!
# Descent of finitely presented modules through a cofiltered limit, general case

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `c` be a limit cone on it. Every sheaf of modules of finite presentation on
`c.pt` is the pullback of one of finite presentation at some stage ([Stacks Project, Tag 01ZR]
(1)), provided that the counit of `pullback ⊣ pushforward` along an affine morphism is an
epimorphism at quasi-coherent modules and that morphisms between pullbacks of finitely presented
modules descend to a later stage ([Stacks Project, Tag 01ZR] (2)).

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.AffinePushforwardFaithful`: pushforward along an affine
  morphism of schemes is faithful on quasi-coherent modules.
* `Stacks.AlgebraicGeometry.ModuleLimits.AffineCounitEpi`: for an affine morphism of schemes the
  counit of `pullback ⊣ pushforward` is an epimorphism at quasi-coherent modules.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_epi_app_of_epi_desc`: if a directed colimit of
  sheaves of modules on a quasi-compact space maps onto a finite-type sheaf, then one of the
  structural maps of the cocone is already an epimorphism.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_finitePresentation_epi_pullback`: for an affine
  morphism `f : X ⟶ Y` of quasi-compact schemes with `Y` quasi-separated, every quasi-coherent
  `𝒪_X`-module of finite type receives an epimorphism from the pullback of an `𝒪_Y`-module of
  finite presentation.
* `Stacks.AlgebraicGeometry.ModuleLimits.affineCounitEpi_of_affinePushforwardFaithful`:
  faithfulness of pushforward along an affine morphism on quasi-coherent modules implies that the
  counit of `pullback ⊣ pushforward` is an epimorphism there.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_inputs`:
  Tag 01ZR (1) in the general qcqs case, from the two inputs described below, and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_card_inputs`:
  the same with the first input replaced by faithfulness of the pushforward.

## Implementation notes

Pick any stage `i`; the projection `c.π.app i` is affine (`AlgebraicGeometry.isAffineHom_π_app'`),
so `c.pt` is quasi-compact. Push `F` forward to the stage, write the pushforward as a directed
colimit of finitely presented modules ([Stacks Project, Tag 01PK],
`AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`), pull back, and use that the
counit of `pullback ⊣ pushforward` is an epimorphism for an affine morphism to get an epimorphism
`p` onto `F` from the pullback of a finitely presented module `G`. Repeat on `kernel p`, which is
quasi-coherent and of finite type, to get an epimorphism `q` from the pullback of a finitely
presented `H`. Descending the composite `q ≫ kernel.ι p` with Tag 01ZR (2) presents `F` as the
pullback of a cokernel on a stage, and a cokernel of a map from a finite-type module to a finitely
presented one is finitely presented (Tag 0H96).

The two inputs are hypotheses of the main results:

* `hepi` (`AffineCounitEpi`) is the part of [Stacks Project, Tag 01SB] that the argument uses:
  for an affine morphism the counit of `pullback ⊣ pushforward` is an epimorphism at
  quasi-coherent modules. It is implied by faithfulness of the pushforward
  (`AffinePushforwardFaithful`).
* `hmap` is [Stacks Project, Tag 01ZR] (2) in the general qcqs case: a morphism between
  pullbacks of finitely presented modules from a stage descends to a later stage.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/- `AlgebraicGeometry.Scheme.Modules` is a plain definition carrying its own `Category`
instance, whose `Hom` field is `AlgebraicGeometry.Scheme.Modules.Hom` rather than
`SheafOfModules.Hom`.  The two categories are definitionally equal but not syntactically, so
instance search — being syntactic — does not transport a hypothesis about a colimit in
`SheafOfModules X.ringCatSheaf` to the corresponding one in `X.Modules`; the three definitions are
made implicitly reducible here so that it does. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory

/-! ### Pushforward along an affine morphism, faithfulness, and the counit -/

/-- Pushforward along an affine morphism of schemes is faithful on quasi-coherent modules (part of
[Stacks Project, Tag 01SB]). -/
def AffinePushforwardFaithful : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] {M N : X.Modules},
    M.IsQuasicoherent → N.IsQuasicoherent → ∀ g h : M ⟶ N,
      (pushforward f).map g = (pushforward f).map h → g = h

/-- For an affine morphism of schemes `f`, the counit of `pullback f ⊣ pushforward f` is an
epimorphism at every quasi-coherent module. -/
def AffineCounitEpi : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules), M.IsQuasicoherent →
    Epi ((pullbackPushforwardAdjunction f).counit.app M)

/-- Faithfulness of pushforward along an affine morphism on quasi-coherent modules implies that
the counit of `pullback f ⊣ pushforward f` is an epimorphism there. -/
theorem affineCounitEpi_of_affinePushforwardFaithful
    (hfaith : AffinePushforwardFaithful.{u}) : AffineCounitEpi.{u} := by
  intro X Y f _ M hMq
  let _ := hMq
  let adj := pullbackPushforwardAdjunction f
  let ε : (Scheme.Modules.pullback f).obj ((pushforward f).obj M) ⟶ M := adj.counit.app M
  have hqc : ((Scheme.Modules.pullback f).obj ((pushforward f).obj M)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback f _ inferInstance
  have hck : (cokernel ε).IsQuasicoherent := by
    let _ := hqc
    infer_instance
  apply Abelian.epi_of_cokernel_π_eq_zero
  refine hfaith f hMq hck (cokernel.π ε) 0 ?_
  rw [Functor.map_zero]
  calc (pushforward f).map (cokernel.π ε)
      = adj.unit.app ((pushforward f).obj M) ≫
          (pushforward f).map ε ≫ (pushforward f).map (cokernel.π ε) := by
        rw [← Category.assoc, adj.right_triangle_components]
        exact (Category.id_comp _).symm
    _ = 0 := by
        rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]

/-! ### One stage of a directed colimit already surjects -/

/-- If a directed colimit of sheaves of modules on a quasi-compact space maps onto a sheaf `M`
of finite type, then already one of the structural maps `φ.app j` is an epimorphism. -/
theorem exists_epi_app_of_epi_desc {X : Scheme.{u}} [CompactSpace X]
    {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (D : J ⥤ X.Modules) (M : X.Modules) [M.IsFiniteType]
    (φ : D ⟶ (Functor.const J).obj M)
    [Epi (colimit.desc D (Cocone.mk M φ))] :
    ∃ j, Epi (φ.app j) := by
  have : IsConnected J := IsFiltered.isConnected J
  let H := image φ
  let ψ := image.ι φ
  let π := factorThruImage φ
  let q : colimit H ⟶ M := colimit.desc H (Cocone.mk M ψ)
  let r := colimit.desc ((Functor.const J).obj M) (constCocone J M)
  have hir : IsIso r := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp
    ⟨isColimitConstCocone J M⟩
  have hqr : q = colim.map ψ ≫ r := by
    apply colimit.hom_ext
    intro j
    simp [q, r, H, constCocone]
  have hmψ : Mono (colim.map ψ) := inferInstance
  have hmr : Mono r := @IsIso.mono_of_iso _ _ _ _ r hir
  have : Mono q := by rw [hqr]; exact @mono_comp _ _ _ _ _ _ hmψ _ hmr
  have hfac : colim.map π ≫ q = colimit.desc D (Cocone.mk M φ) := by
    apply colimit.hom_ext
    intro j
    simp [q, H, π, ψ, image.fac]
  have : Epi (colim.map π ≫ q) := hfac.symm ▸ inferInstance
  have : Epi q := epi_of_epi (colim.map π) q
  have : IsIso q := isIso_of_mono_of_epi q
  have : (colimit H).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso q).symm
  obtain ⟨j, hj⟩ :=
    Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType X.ringCatSheaf H
  have : Epi (colimit.ι H j) := hj
  have : Epi (π.app j) := inferInstance
  refine ⟨j, ?_⟩
  rw [show φ.app j = π.app j ≫ colimit.ι H j ≫ q by
    simp [q, H, ← NatTrans.comp_app, π, ψ, image.fac]]
  infer_instance

/-! ### A finitely presented module on the target surjects onto a finite-type module -/

/-- For an affine morphism `f : X ⟶ Y` between quasi-compact schemes with `Y` quasi-separated,
every quasi-coherent `𝒪_X`-module `M` of finite type receives an epimorphism from the pullback
of an `𝒪_Y`-module of finite presentation, provided the counit of `pullback ⊣ pushforward` along
affine morphisms is an epimorphism at quasi-coherent modules. -/
theorem exists_finitePresentation_epi_pullback (hepi : AffineCounitEpi.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [CompactSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ G : Y.Modules, G.IsFinitePresentation ∧
      ∃ p : (Scheme.Modules.pullback f).obj G ⟶ M, Epi p := by
  obtain ⟨J, _, _, _, E, φ, hE, ⟨hc⟩⟩ :=
    _root_.AlgebraicGeometry.exists_directed_system_of_isFinitePresentation Y
      ((pushforward f).obj M)
  let ε : (Scheme.Modules.pullback f).obj ((pushforward f).obj M) ⟶ M :=
    (pullbackPushforwardAdjunction f).counit.app M
  have : Epi ε := hepi f M inferInstance
  let T := E ⋙ Scheme.Modules.pullback f
  let c := (Scheme.Modules.pullback f).mapCocone (Cocone.mk _ φ)
  have hc' : IsColimit c := isColimitOfPreserves (Scheme.Modules.pullback f) hc
  let θ : T ⟶ (Functor.const J).obj M :=
    { app := fun j => (Scheme.Modules.pullback f).map (φ.app j) ≫ ε
      naturality := by
        intro j k g
        change (Scheme.Modules.pullback f).map (E.map g) ≫
          (Scheme.Modules.pullback f).map (φ.app k) ≫ ε = _
        rw [← Category.assoc, ← Functor.map_comp]
        simp [φ.naturality] }
  have hi : IsIso (colimit.desc T c) :=
    (colimit.isColimit T).nonempty_isColimit_iff_isIso_desc.mp ⟨hc'⟩
  have eq : colimit.desc T (Cocone.mk M θ) = colimit.desc T c ≫ ε := by
    apply colimit.hom_ext
    intro j
    simp [θ, c]
  have : Epi (colimit.desc T (Cocone.mk M θ)) := by rw [eq]; infer_instance
  obtain ⟨j, hj⟩ := exists_epi_app_of_epi_desc T M θ
  exact ⟨E.obj j, hE j, θ.app j, hj⟩

/-! ### Tag 01ZR (1) in the general quasi-compact quasi-separated case -/

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- **Stacks Project, Tag 01ZR (1)**, general quasi-compact quasi-separated case. Assume that the
counit of `pullback ⊣ pushforward` along an affine morphism is an epimorphism at quasi-coherent
modules (`hepi`) and that morphisms between pullbacks of finitely presented modules descend to a
later stage (Tag 01ZR (2), `hmap`). Then a finitely presented module on the limit of a cofiltered
system of quasi-compact and quasi-separated schemes with affine transition morphisms is the
pullback of a finitely presented module at some stage. -/
theorem exists_isFinitePresentation_pullback_iso_of_inputs
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hepi : AffineCounitEpi.{u})
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫
            (pullbackComp (c.π.app j) (D.map e)).hom.app G ≫
            (pullbackCongr (c.w e)).hom.app G =
          (pullbackComp (c.π.app j) (D.map e)).hom.app F ≫
            (pullbackCongr (c.w e)).hom.app F ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) := by
  classical
  let i : I := IsCofiltered.nonempty.some
  let f : c.pt ⟶ D.obj i := c.π.app i
  have hfa : IsAffineHom f := isAffineHom_π_app' D c hc i
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit' D c hc
  obtain ⟨G, hG, p, hp⟩ := exists_finitePresentation_epi_pullback hepi f F
  have : G.IsFinitePresentation := hG
  have : Epi p := hp
  have hGp : ((Scheme.Modules.pullback f).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback f G
  have hkq : (kernel p).IsQuasicoherent := by
    let _ : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
      Stacks.Modules.isQuasicoherent_pullback f G inferInstance
    infer_instance
  have hkt : (kernel p).IsFiniteType := by
    let _ := hGp
    exact Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType p
  obtain ⟨H, hH, q, hq⟩ :=
    exists_finitePresentation_epi_pullback hepi f (kernel p)
  have : H.IsFinitePresentation := hH
  have : Epi q := hq
  let φ := q ≫ kernel.ι p
  obtain ⟨j, e, φj, hφj⟩ := hmap i H G hH hG φ
  have hHe : ((Scheme.Modules.pullback (D.map e)).obj H).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) H
  have hGe : ((Scheme.Modules.pullback (D.map e)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) G
  have hfp : (cokernel φj).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel φj
  refine ⟨j, cokernel φj, hfp, ?_⟩
  let E (K : (D.obj i).Modules) :=
    (pullbackComp (c.π.app j) (D.map e)).app K ≪≫ (pullbackCongr (c.w e)).app K
  let eC : cokernel ((Scheme.Modules.pullback (c.π.app j)).map φj) ≅ cokernel φ :=
    cokernel.mapIso _ _ (E H) (E G) hφj
  let hpC : IsColimit (CokernelCofork.ofπ p (kernel.condition p)) :=
    Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι p) (kernel.condition p)) (kernelIsKernel p)
  let eF : cokernel φ ≅ F :=
    cokernelEpiComp q (kernel.ι p) ≪≫
      (cokernelIsCokernel (kernel.ι p)).coconePointUniqueUpToIso hpC
  exact ⟨eF.symm ≪≫ eC.symm ≪≫
    (PreservesCokernel.iso (Scheme.Modules.pullback (c.π.app j)) φj).symm⟩

/-- **Stacks Project, Tag 01ZR (1)**, general quasi-compact quasi-separated case, assuming that
pushforward along an affine morphism is faithful on quasi-coherent modules (`hfaith`, part of
[Stacks Project, Tag 01SB]) and Tag 01ZR (2) (`hmap`): a finitely presented module on the limit of
a cofiltered system of quasi-compact and quasi-separated schemes with affine transition morphisms
is the pullback of a finitely presented module at some stage. -/
theorem exists_isFinitePresentation_pullback_iso_of_card_inputs
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hfaith : AffinePushforwardFaithful.{u})
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫
            (pullbackComp (c.π.app j) (D.map e)).hom.app G ≫
            (pullbackCongr (c.w e)).hom.app G =
          (pullbackComp (c.π.app j) (D.map e)).hom.app F ≫
            (pullbackCongr (c.w e)).hom.app F ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_inputs D c hc
    (affineCounitEpi_of_affinePushforwardFaithful hfaith) hmap F

end Stacks.AlgebraicGeometry.ModuleLimits

end
