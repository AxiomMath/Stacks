module

public import StacksFrontier.AlgebraicGeometry.Modules.CechKunnethFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleRefinementPullback
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# Künneth injectivity on first Čech cohomology for a module trivial on the product

Let `k` be a field, `P = X ×_k Y`, with the box cover `W` of `P` built from covers `U` of `X` and
`V` of `Y`, and faces `j₁ : Y ⟶ P`, `j₂ : X ⟶ P` through rational points. For a module `F` on `P`
isomorphic to `𝒪_P`, a Čech `1`-cocycle of `F` on `W` is a coboundary as soon as its pullbacks
along the two faces are coboundaries. This transports
`Stacks.Cech.Kunneth.exists_cechD_eq_of_faces` along `F ≅ 𝒪_P`, and is the fibre input of
the proof of [Stacks, Tag 0BF3] used for [Stacks, Tag 0BF4].

## Main results

* `Stacks.Cech.pullbackSections_naturality`, `Stacks.Cech.pullbackUnitIso_hom_app_pullbackSections`
* `Stacks.Cech.cochainPullback_cochainMap`
* `Stacks.Cech.Kunneth.exists_cechD_eq_of_faces_of_iso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Cech

/-- The canonical map on sections induced by a morphism of schemes is natural in the module. -/
theorem pullbackSections_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {F G : Y.Modules} (t : F ⟶ G)
    (V : Y.Opens) (s : Γ(F, V)) :
    pullbackSections f G V (t.app V s) =
      ((Scheme.Modules.pullback f).map t).app (f ⁻¹ᵁ V) (pullbackSections f F V s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality t
  exact congr($(congrArg (fun k => Scheme.Modules.Hom.app k V) h) s)

/-- **The pullback of a function, as a section of the pullback of `𝒪`, is its pullback as a
function.** -/
theorem pullbackUnitIso_hom_app_pullbackSections {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (s : Γ(Y, V)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ V)
      (pullbackSections f (Scheme.unitModule Y) V (show Γ(Scheme.unitModule Y, V) from s)) =
        f.app V s := by
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      f.toRingCatSheafHom
  exact congr($(congrArg (fun k => Scheme.Modules.Hom.app k V) h) s)

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {I I' : Type u} (U : I → X.Opens)
  (W : I' → X'.Opens) (π : I' → I) (hW : ∀ k, W k ≤ g ⁻¹ᵁ U (π k))

/-- **Pulling Čech cochains back is natural in the module.** -/
theorem cochainPullback_cochainMap {F G : X.Modules} (t : F ⟶ G) (p : ℕ)
    (s : CechCochains.Cochain U F.presheaf p) :
    cochainPullback g U W π hW G p (cochainMap U t.mapPresheaf p s) =
      cochainMap W ((Scheme.Modules.pullback g).map t).mapPresheaf p
        (cochainPullback g U W π hW F p s) := by
  funext k
  show CechCochains.restr _ _ (pullbackSections g G _ (t.app _ (s (π ∘ k)))) =
    ((Scheme.Modules.pullback g).map t).app _ (CechCochains.restr _ _ _)
  rw [pullbackSections_naturality]
  exact restr_app ((Scheme.Modules.pullback g).map t).mapPresheaf _ _

/-- **Pulling back Čech cochains of `𝒪`**: through `pullbackUnitIso`, the pullback of a cochain of
functions is the cochain of pulled back functions. -/
theorem pullbackUnitIso_cochainPullback (p : ℕ)
    (s : CechCochains.Cochain U (Kunneth.OM X).presheaf p)
    (k : Fin (p + 1) → I') :
    (Scheme.Modules.pullbackUnitIso g).hom.app (CechCochains.inter W k)
        (cochainPullback g U W π hW (Kunneth.OM X) p s k) =
      g.appLE (CechCochains.inter U (π ∘ k)) (CechCochains.inter W k)
        (inter_le_preimage_inter g U W π hW k) (s (π ∘ k)) := by
  show (Scheme.Modules.pullbackUnitIso g).hom.mapPresheaf.app _ (CechCochains.restr _ _ _) = _
  refine (restr_app (Scheme.Modules.pullbackUnitIso g).hom.mapPresheaf
    (inter_le_preimage_inter g U W π hW k) _).symm.trans ?_
  refine (congrArg (CechCochains.restr (Kunneth.OM X').presheaf
    (inter_le_preimage_inter g U W π hW k))
    (pullbackUnitIso_hom_app_pullbackSections g _ (s (π ∘ k)))).trans ?_
  rfl

end Stacks.Cech

namespace Stacks.Cech.Kunneth

variable {k : Type u} [Field k] {X Y P : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
  {r : P ⟶ X} {q : P ⟶ Y} {I J : Type u}

/-- A morphism of modules commutes with the Čech differential on cochains, as an identity of
functions. -/
private theorem cochainMap_iso_inv_hom {T : Scheme.{u}} {K : Type u} (W : K → T.Opens)
    {F G : T.Modules} (ε : F ≅ G) (p : ℕ) (z : CechCochains.Cochain W F.presheaf p) :
    cochainMap W ε.inv.mapPresheaf p (cochainMap W ε.hom.mapPresheaf p z) = z := by
  funext i
  show (ε.inv.app _) ((ε.hom.app _) (z i)) = z i
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ε.hom_inv_id]
  rfl

/-- The pullback along a face of a cochain of a trivialised module, read through the
trivialisation, is the restriction of the cochain of functions along the face. -/
private theorem face_transport {T : Scheme.{u}} {K K' : Type u} (j : T ⟶ P) (W' : K → P.Opens)
    (Vc : K' → T.Opens) (π : K' → K) (hW : ∀ b, Vc b ≤ j ⁻¹ᵁ W' (π b)) (F : P.Modules)
    (ε : F ≅ Scheme.unitModule P) (z : CechCochains.Cochain W' F.presheaf 1) :
    cochainMap Vc ((Scheme.Modules.pullback j).map ε.hom ≫
        (Scheme.Modules.pullbackUnitIso j).hom).mapPresheaf 1
      (cochainPullback j W' Vc π hW F 1 z) = fun b =>
      j.appLE (CechCochains.inter W' (π ∘ b)) (CechCochains.inter Vc b)
        (inter_le_preimage_inter j W' Vc π hW b)
        (cochainMap W' ε.hom.mapPresheaf 1 z (π ∘ b)) := by
  have h1 : cochainMap Vc ((Scheme.Modules.pullback j).map ε.hom ≫
      (Scheme.Modules.pullbackUnitIso j).hom).mapPresheaf 1
        (cochainPullback j W' Vc π hW F 1 z) =
      cochainMap Vc (Scheme.Modules.pullbackUnitIso j).hom.mapPresheaf 1
        (cochainMap Vc ((Scheme.Modules.pullback j).map ε.hom).mapPresheaf 1
          (cochainPullback j W' Vc π hW F 1 z)) := rfl
  rw [h1, ← cochainPullback_cochainMap]
  funext b
  exact pullbackUnitIso_cochainPullback j W' Vc π hW 1 _ b

/-- A coboundary of the pullback along a face of a cocycle of a trivialised module gives, through
the trivialisation, a coboundary of any cochain of functions equal to the restricted cocycle. -/
private theorem exists_cechD_eq_of_pullback_iso {T : Scheme.{u}} {K K' : Type u} (j : T ⟶ P)
    (W' : K → P.Opens) (Vc : K' → T.Opens) (π : K' → K) (hW : ∀ b, Vc b ≤ j ⁻¹ᵁ W' (π b))
    (F : P.Modules) (ε : F ≅ Scheme.unitModule P) (z : CechCochains.Cochain W' F.presheaf 1)
    (τ : CechCochains.Cochain Vc (OM T).presheaf 1)
    (hτ : ∀ b, j.appLE (CechCochains.inter W' (π ∘ b)) (CechCochains.inter Vc b)
      (inter_le_preimage_inter j W' Vc π hW b) (cochainMap W' ε.hom.mapPresheaf 1 z (π ∘ b)) = τ b)
    (h : ∃ t : CechCochains.Cochain Vc ((Scheme.Modules.pullback j).obj F).presheaf 0,
      CechCochains.cechD Vc _ 0 t = cochainPullback j W' Vc π hW F 1 z) :
    ∃ t : CechCochains.Cochain Vc (OM T).presheaf 0, CechCochains.cechD Vc _ 0 t = τ := by
  obtain ⟨t, ht⟩ := h
  refine ⟨cochainMap Vc ((Scheme.Modules.pullback j).map ε.hom ≫
    (Scheme.Modules.pullbackUnitIso j).hom).mapPresheaf 0 t, ?_⟩
  exact (cochainMap_cechD Vc _ 0 t).symm.trans ((congrArg (cochainMap Vc _ 1) ht).trans
    ((face_transport j W' Vc π hW F ε z).trans (funext hτ)))

variable (H : IsPullback r q f g) (U : I → X.Opens) (V : J → Y.Opens)

include H in
/-- **Künneth injectivity on first Čech cohomology, for a module trivial on the product.** In the
situation of `Stacks.Cech.Kunneth.exists_cechD_eq_of_faces`, let `F` be a module on `P` with
`F ≅ 𝒪_P`. A Čech `1`-cocycle of `F` on the box cover `W'` is a coboundary as soon as its
pullbacks along the two faces, on the covers `U` and `V` refining the inverse images of `W'`, are
coboundaries. -/
theorem exists_cechD_eq_of_faces_of_iso [Finite I] [Finite J] (W' : I × J → P.Opens)
    (hle : ∀ t : I × J, box r q U V ![t.1] ![t.2] ≤ W' t)
    (hge : ∀ t : I × J, W' t ≤ box r q U V ![t.1] ![t.2])
    (hUa : ∀ (m : ℕ) (a : Fin (m + 1) → I), IsAffineOpen (CechCochains.inter U a))
    (hVa : ∀ (n : ℕ) (b : Fin (n + 1) → J), IsAffineOpen (CechCochains.inter V b))
    (hWa : ∀ (m n : ℕ) (a : Fin (m + 1) → I) (b : Fin (n + 1) → J),
      IsAffineOpen (box r q U V a b))
    (hU : ⊤ ≤ ⨆ a, U a) (hV : ⊤ ≤ ⨆ b, V b)
    (hΓX : Function.Bijective (globalRingHom f).hom)
    (hΓY : Function.Bijective (globalRingHom g).hom)
    (x0 : Spec (.of k) ⟶ X) (hx0 : x0 ≫ f = 𝟙 _) (a0 : I) (ha0 : x0 ⁻¹ᵁ U a0 = ⊤)
    (j1 : Y ⟶ P) (hj1r : j1 ≫ r = g ≫ x0) (hj1q : j1 ≫ q = 𝟙 Y)
    (y0 : Spec (.of k) ⟶ Y) (hy0 : y0 ≫ g = 𝟙 _) (b0 : J) (hb0 : y0 ⁻¹ᵁ V b0 = ⊤)
    (j2 : X ⟶ P) (hj2r : j2 ≫ r = 𝟙 X) (hj2q : j2 ≫ q = f ≫ y0)
    (hW1 : ∀ b, V b ≤ j1 ⁻¹ᵁ W' (a0, b)) (hW2 : ∀ a, U a ≤ j2 ⁻¹ᵁ W' (a, b0))
    (F : P.Modules) (ε : F ≅ Scheme.unitModule P) (z : CechCochains.Cochain W' F.presheaf 1)
    (hz : CechCochains.cechD W' F.presheaf 1 z = 0)
    (h1 : ∃ t : CechCochains.Cochain V ((Scheme.Modules.pullback j1).obj F).presheaf 0,
      CechCochains.cechD V _ 0 t = cochainPullback j1 W' V (fun b => (a0, b)) hW1 F 1 z)
    (h2 : ∃ t : CechCochains.Cochain U ((Scheme.Modules.pullback j2).obj F).presheaf 0,
      CechCochains.cechD U _ 0 t = cochainPullback j2 W' U (fun a => (a, b0)) hW2 F 1 z) :
    ∃ e : CechCochains.Cochain W' F.presheaf 0, CechCochains.cechD W' F.presheaf 0 e = z := by
  set ζ := cochainMap W' ε.hom.mapPresheaf 1 z with hζ
  have hζz : CechCochains.cechD W' (OM P).presheaf 1 ζ = 0 := by
    have h := cochainMap_cechD W' ε.hom.mapPresheaf 1 z
    rw [hz, map_zero] at h
    exact h.symm
  obtain ⟨e', he'⟩ := exists_cechD_eq_of_faces H U V y0 hy0 b0 hb0 j2 hj2r hj2q x0 hx0 a0 ha0 j1
    hj1r hj1q W' hle hge hUa hVa hWa hU hV hΓX hΓY ζ hζz
    (exists_cechD_eq_of_pullback_iso j2 W' U _ hW2 F ε z _ (fun a => by
      exact (congr($(Scheme.Hom.map_appLE j2 (le_face2 U V y0 b0 hb0 j2 hj2r hj2q a)
        (homOfLE ((box_mono r q U V (a' := a) (b' := fun _ => (![b0] : Fin 1 → J) 0)
          (fun k => ⟨k, rfl⟩) (fun _ => ⟨0, rfl⟩)).trans (box_le_inter r q U V W' hle
            (fun i => (a i, (![b0] : Fin 1 → J) 0))))).op) (ζ fun i => (a i, b0)))).symm) h2)
    (exists_cechD_eq_of_pullback_iso j1 W' V _ hW1 F ε z _ (fun b => by
      exact (congr($(Scheme.Hom.map_appLE j1 (le_face1 U V x0 a0 ha0 j1 hj1r hj1q b)
        (homOfLE ((box_mono r q U V (a' := fun _ => (![a0] : Fin 1 → I) 0) (b' := b)
          (fun _ => ⟨0, rfl⟩) (fun k => ⟨k, rfl⟩)).trans (box_le_inter r q U V W' hle
            (fun i => ((![a0] : Fin 1 → I) 0, b i))))).op) (ζ fun i => (a0, b i)))).symm) h1)
  refine ⟨cochainMap W' ε.inv.mapPresheaf 0 e', ?_⟩
  refine (cochainMap_cechD W' ε.inv.mapPresheaf 0 e').symm.trans ?_
  have h3 : cochainMap W' ε.inv.mapPresheaf 1 ζ = z := cochainMap_iso_inv_hom W' ε 1 z
  exact (congrArg (cochainMap W' ε.inv.mapPresheaf 1) he').trans h3

end Stacks.Cech.Kunneth

end
