module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageTriple
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeComp

/-!
# The stage bridge of [Stacks, Tag 0EXD] is compatible with composition

The stage functors of [Stacks, Tag 0EXB] commute with the transition functors of
[Stacks, Tag 0EXE] by `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso` (on all sheaves
of modules) and `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` (on the finite locally free
modules).  This file proves that these commutations are **compatible with composition**: for
`f : X ⟶ Y` and `g : Y ⟶ W`, the bridge of `f ≫ g` is the bridge of `g` carried along the
transition functor of `f` followed by the bridge of `f`, up to the composition comparisons of the
transition functors and of the inverse images.  That is the single-stage coherence the comparison
functor of [Stacks, Tag 0EXD] needs at a stage object (item 1b of the roadmap in
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean`), and, applied to
the two routes around a commutative square, it identifies the bridges' transport of
`AlgebraicGeometry.vectPullbackSquareIso` with
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`.

## Main definitions

* `Stacks.SheafOfModules.pullbackCompOfEq`: Mathlib's `CategoryTheory.SheafOfModules.pullbackComp`
  followed by the transport to a morphism of sheaves of rings equal to the composite, read at a
  site functor equal to the composite site functor.

## Main results

* `Stacks.SheafOfModules.pullbackCompOfEq_assoc_app`: its associativity pentagon, with all
  composites given as parameters.
* `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso_comp`: **the stage bridge is
  compatible with composition**, on all sheaves of modules.
* `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_comp`: the same on the finite locally free
  modules.

## Implementation notes

The bridge is a contraction `pullbackComp ι_Y c_f`, a transport along the stage formula, and the
inverse of a contraction `pullbackComp ρ_f ι_X`; the two contractions are read at *different*
site functors (`Opens.map (𝟙 Y) ⋙ Opens.map f` and `Opens.map f ⋙ Opens.map (𝟙 X)`), which are
equal only definitionally.  A pentagon argument that rewrites with Mathlib's
`CategoryTheory.SheafOfModules.pullback_assoc` directly therefore never matches syntactically.
`Stacks.SheafOfModules.pullbackCompOfEq` takes both the composite morphism and the composite
site functor as parameters, so that each composite `𝒪 ⟶ colim_F 𝒪` is given **one** spelling —
`ι ≫ c`, at the site functor `Opens.map` of a single morphism of schemes — throughout the
computation; then the three pentagons of the chains `(ι_W, c_g, c_f)`, `(ρ_g, ι_Y, c_f)` and
`(ρ_g, ρ_f, ι_X)` share their terms literally and telescope
(`AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso_comp_aux`).

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {R' : Sheaf K' RingCat.{u}}
  {R'' : Sheaf K'' RingCat.{u}}

/-- **Extension of scalars along two composable morphisms of sheaves of rings is extension of
scalars along a morphism equal to their composite**, the composite being read at an arbitrary
site functor `Fc` equal to `F ⋙ G`.  Both the site functor and the morphism are parameters, so
that one composite can be given one spelling throughout a computation, and a proof may
substitute the two equations. -/
noncomputable def pullbackCompOfEq {F : C ⥤ D} {G : D ⥤ D'} {Fc : C ⥤ D'}
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
    [Functor.IsContinuous (F ⋙ G) J K'] [Functor.IsContinuous Fc J K']
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
    (χ : S ⟶ (Fc.sheafPushforwardContinuous RingCat.{u} J K').obj R')
    [(_root_.SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} χ).IsRightAdjoint]
    (hF : F ⋙ G = Fc)
    (hχ : HEq χ (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) :
    _root_.SheafOfModules.pullback.{v} φ ⋙ _root_.SheafOfModules.pullback.{v} ψ ≅
      _root_.SheafOfModules.pullback.{v} χ :=
  _root_.SheafOfModules.pullbackComp.{v} φ ψ ≪≫
    eqToIso (by subst hF; obtain rfl := eq_of_heq hχ; rfl)

/-- At the composite itself, `Stacks.SheafOfModules.pullbackCompOfEq` is Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp`. -/
lemma pullbackCompOfEq_self {F : C ⥤ D} {G : D ⥤ D'}
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
    [Functor.IsContinuous (F ⋙ G) J K']
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
    [(_root_.SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ψ).IsRightAdjoint] :
    pullbackCompOfEq.{v} φ ψ (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)
        rfl HEq.rfl =
      _root_.SheafOfModules.pullbackComp.{v} φ ψ :=
  Iso.trans_refl _

/-- **The associativity pentagon of `Stacks.SheafOfModules.pullbackCompOfEq`**, on components.
Substituting the equations that define the composites leaves Mathlib's
`CategoryTheory.SheafOfModules.pullback_assoc`. -/
lemma pullbackCompOfEq_assoc_app {F : C ⥤ D} {G : D ⥤ D'} {H : D' ⥤ D''}
    {Fab : C ⥤ D'} {Gbc : D ⥤ D''} {Fabc : C ⥤ D''}
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
    [Functor.IsContinuous H K' K'']
    [Functor.IsContinuous (F ⋙ G) J K'] [Functor.IsContinuous (G ⋙ H) K K'']
    [Functor.IsContinuous (F ⋙ Gbc) J K''] [Functor.IsContinuous (Fab ⋙ H) J K'']
    [Functor.IsContinuous Fab J K'] [Functor.IsContinuous Gbc K K'']
    [Functor.IsContinuous Fabc J K'']
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (b : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
    (c : R' ⟶ (H.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')
    (ab : S ⟶ (Fab.sheafPushforwardContinuous RingCat.{u} J K').obj R')
    (bc : R ⟶ (Gbc.sheafPushforwardContinuous RingCat.{u} K K'').obj R'')
    (d : S ⟶ (Fabc.sheafPushforwardContinuous RingCat.{u} J K'').obj R'')
    [(_root_.SheafOfModules.pushforward.{v} a).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} b).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} c).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} ab).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} bc).IsRightAdjoint]
    [(_root_.SheafOfModules.pushforward.{v} d).IsRightAdjoint]
    (hFab : F ⋙ G = Fab) (hGbc : G ⋙ H = Gbc) (hd₁ : F ⋙ Gbc = Fabc) (hd₂ : Fab ⋙ H = Fabc)
    (hab : HEq ab (a ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map b))
    (hbc : HEq bc (b ≫ (G.sheafPushforwardContinuous RingCat.{u} K K').map c))
    (hd : HEq d (a ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map bc))
    (hd' : HEq d (ab ≫ (Fab.sheafPushforwardContinuous RingCat.{u} J K').map c))
    (M : _root_.SheafOfModules.{v} S) :
    (pullbackCompOfEq.{v} b c bc hGbc hbc).hom.app
          ((_root_.SheafOfModules.pullback.{v} a).obj M) ≫
        (pullbackCompOfEq.{v} a bc d hd₁ hd).hom.app M =
      (_root_.SheafOfModules.pullback.{v} c).map
          ((pullbackCompOfEq.{v} a b ab hFab hab).hom.app M) ≫
        (pullbackCompOfEq.{v} ab c d hd₂ hd').hom.app M := by
  subst hFab hGbc hd₁
  obtain rfl := eq_of_heq hab
  obtain rfl := eq_of_heq hbc
  obtain rfl := eq_of_heq hd
  have key := NatTrans.congr_app (congrArg Iso.hom
    (_root_.SheafOfModules.pullback_assoc.{v} a b c)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at key
  simp only [pullbackCompOfEq, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Category.assoc]
  exact key

end Stacks.SheafOfModules


namespace AlgebraicGeometry

open Stacks.SheafOfModules (pullbackCompOfEq pullbackCompOfEq_self pullbackCompOfEq_assoc_app)

/-! ### The stage bridge is compatible with composition -/

section Comp

variable (p : ℕ) [Fact p.Prime] {X Y W : Scheme.{u}}

/-- The components of `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso`, written out. -/
lemma frobeniusStageExtendScalarsPullbackIso_hom_app (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ)
        (N : _root_.SheafOfModules.{u} Y.ringSheafOnOpens) :
    (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom.app N =
      (_root_.SheafOfModules.pullbackComp.{u} (frobeniusStageStructureMap Y p hY n)
          (frobeniusColimitStructureSheafHom p f hX hY)).hom.app N ≫
        (eqToIso (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ)
          (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n))).hom.app N ≫
          (_root_.SheafOfModules.pullbackComp.{u} f.ringSheafOnOpensHom
            (frobeniusStageStructureMap X p hX n)).inv.app N := rfl

/-- **The stage bridge as one contraction followed by the inverse of another.**  The composite
`𝒪_Y ⟶ f_*(colim_F 𝒪_X)` both contractions are read at is `ι_Y ≫ c_f`, at the site functor of
`f`; the transport along the stage formula that the bridge carries becomes the second
contraction's transport. -/
lemma frobeniusStageExtendScalarsPullbackIso_hom_app_eq (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ)
        (N : _root_.SheafOfModules.{u} Y.ringSheafOnOpens) :
    (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom.app N =
      (pullbackCompOfEq.{u} (Fc := Opens.map f.base)
          (frobeniusStageStructureMap Y p hY n) (frobeniusColimitStructureSheafHom p f hX hY)
          (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY) rfl
          HEq.rfl).hom.app N ≫
        (pullbackCompOfEq.{u} (Fc := Opens.map f.base)
          f.ringSheafOnOpensHom (frobeniusStageStructureMap X p hX n)
          (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY) rfl
          (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY
            n))).inv.app N := by
  rw [frobeniusStageExtendScalarsPullbackIso_hom_app]
  simp only [pullbackCompOfEq, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Category.assoc, eqToIso.hom, eqToIso.inv]
  rfl

/-- The algebra behind `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso_comp`, in an
arbitrary category: three pentagon identities telescope. -/
lemma frobeniusStageExtendScalarsPullbackIso_comp_aux {E E' D : Type*} [Category E]
    [Category E'] [Category D] (F : E ⥤ D) (G : E' ⥤ D)
    {e₀ e₁ e₂ : E} {e₅ e₆ : E'} {d₀ d₃ d₇ : D}
    {k₁ : e₀ ⟶ e₁} {i₁ : e₂ ⟶ e₁} {i₁' : e₁ ⟶ e₂} {k₂ : F.obj e₂ ⟶ d₃} {i₂ : G.obj e₅ ⟶ d₃}
    {i₂' : d₃ ⟶ G.obj e₅} {m : e₅ ⟶ e₆} {x₁ : F.obj e₁ ⟶ d₇} {x₂ : d₃ ⟶ d₇}
    {pc : F.obj e₀ ⟶ d₀} {k₃ : d₀ ⟶ d₇} {k₃' : G.obj e₆ ⟶ d₇} {k₃'' : d₇ ⟶ G.obj e₆}
    (h₁ : pc ≫ k₃ = F.map k₁ ≫ x₁) (h₂ : k₂ ≫ x₂ = F.map i₁ ≫ x₁)
    (h₃ : i₂ ≫ x₂ = G.map m ≫ k₃') (hi₁ : i₁' ≫ i₁ = 𝟙 _) (hi₂ : i₂' ≫ i₂ = 𝟙 _)
    (hk₃ : k₃' ≫ k₃'' = 𝟙 _) :
    F.map (k₁ ≫ i₁') ≫ (k₂ ≫ i₂') ≫ G.map m = pc ≫ k₃ ≫ k₃'' := by
  have h₃' : i₂' ≫ G.map m = x₂ ≫ k₃'' := by
    have := congrArg (fun t => i₂' ≫ t ≫ k₃'') h₃
    simp only [reassoc_of% hi₂, Category.assoc, hk₃, Category.comp_id] at this
    exact this.symm
  rw [Category.assoc, h₃', reassoc_of% h₂, ← Functor.map_comp_assoc, Category.assoc, hi₁,
    Category.comp_id, reassoc_of% h₁]

/-- The stage formula of `f ≫ g`, read through the composition of the canonical morphisms of
Frobenius colimits: `ι_W ≫ c_{f ≫ g} = (ι_W ≫ c_g) ≫ g_*(c_f)`. -/
lemma frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp (f : X ⟶ Y) (g : Y ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
    (n : ℕ) :
    frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW =
      (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW) ≫
        (g.ringSheafPushforward).map (frobeniusColimitStructureSheafHom p f hX hY) := by
  rw [frobeniusColimitStructureSheafHom_comp p f g hX hY hW]
  exact (Category.assoc _ _ _).symm

/-- The stage formula of `f ≫ g`, read through the stage formula of `g`:
`ι_W ≫ c_{f ≫ g} = ρ_g ≫ g_*(ι_Y ≫ c_f)`. -/
lemma frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp' (f : X ⟶ Y) (g : Y ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
    (n : ℕ) :
    frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW =
      g.ringSheafOnOpensHom ≫ (g.ringSheafPushforward).map
        (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY) := by
  rw [frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp p f g hX hY hW,
    frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p g hY hW n, Category.assoc,
    ← Functor.map_comp]

section CompPieces

variable (f : X ⟶ Y) (g : Y ⟶ W)
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
  (n : ℕ) (N : _root_.SheafOfModules.{u} W.ringSheafOnOpens)

set_option maxHeartbeats 1600000 in
/-- The pentagon of the chain `(ι_W, c_g, c_f)`. -/
lemma frobeniusStageExtendScalarsPullbackIso_comp_pentagon₁ :
    (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base)
          (frobeniusColimitStructureSheafHom p g hY hW)
          (frobeniusColimitStructureSheafHom p f hX hY)
          (frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
          (heq_of_eq (frobeniusColimitStructureSheafHom_comp p f g hX hY hW))).hom.app
        ((_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap W p hW n)).obj N) ≫
        (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) (frobeniusStageStructureMap W p hW n)
          (frobeniusColimitStructureSheafHom p (f ≫ g) hX hW)
          (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
          HEq.rfl).hom.app N =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY)).map
          ((pullbackCompOfEq.{u} (Fc := Opens.map g.base) (frobeniusStageStructureMap W p hW n)
              (frobeniusColimitStructureSheafHom p g hY hW)
              (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW) rfl
              HEq.rfl).hom.app N) ≫ (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW)
            (frobeniusColimitStructureSheafHom p f hX hY)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
            (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp p f g hX hY hW
                n))).hom.app N :=
  pullbackCompOfEq_assoc_app.{u} (Fab := Opens.map g.base)
    (Gbc := Opens.map (f ≫ g).base) (Fabc := Opens.map (f ≫ g).base)
    (frobeniusStageStructureMap W p hW n) (frobeniusColimitStructureSheafHom p g hY hW)
        (frobeniusColimitStructureSheafHom p f hX hY) (frobeniusColimitι W p hW n ≫
          frobeniusColimitStructureSheafHom p g hY hW) (frobeniusColimitStructureSheafHom p (f ≫ g)
          hX hW) (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW)
        rfl rfl rfl rfl HEq.rfl (heq_of_eq (frobeniusColimitStructureSheafHom_comp p f g hX hY hW))
        HEq.rfl (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp p f g hX
            hY hW n)) N

/-- The pentagon of the chain `(ρ_g, ι_Y, c_f)`. -/
lemma frobeniusStageExtendScalarsPullbackIso_comp_pentagon₂ :
    (pullbackCompOfEq.{u} (Fc := Opens.map f.base) (frobeniusStageStructureMap Y p hY n)
          (frobeniusColimitStructureSheafHom p f hX hY)
          (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY) rfl
          HEq.rfl).hom.app ((_root_.SheafOfModules.pullback.{u} g.ringSheafOnOpensHom).obj N) ≫
        (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) g.ringSheafOnOpensHom
          (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY)
          (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
          (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp' p f g hX hY hW
              n))).hom.app N =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY)).map
          ((pullbackCompOfEq.{u} (Fc := Opens.map g.base) g.ringSheafOnOpensHom
              (frobeniusStageStructureMap Y p hY n) (frobeniusColimitι W p hW n ≫
                frobeniusColimitStructureSheafHom p g hY hW) rfl
              (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p g hY hW
                  n))).hom.app N) ≫ (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW)
            (frobeniusColimitStructureSheafHom p f hX hY)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
            (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp p f g hX hY hW
                n))).hom.app N :=
  pullbackCompOfEq_assoc_app.{u} (Fab := Opens.map g.base)
    (Gbc := Opens.map f.base) (Fabc := Opens.map (f ≫ g).base)
    g.ringSheafOnOpensHom (frobeniusStageStructureMap Y p hY n)
        (frobeniusColimitStructureSheafHom p f hX hY) (frobeniusColimitι W p hW n ≫
          frobeniusColimitStructureSheafHom p g hY hW) (frobeniusColimitι Y p hY n ≫
          frobeniusColimitStructureSheafHom p f hX hY) (frobeniusColimitι W p hW n ≫
          frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl rfl rfl rfl
        (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p g hY hW n)) HEq.rfl
        (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp' p f g hX hY hW
            n)) (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp p f g hX
            hY hW n)) N

/-- The pentagon of the chain `(ρ_g, ρ_f, ι_X)`. -/
lemma frobeniusStageExtendScalarsPullbackIso_comp_pentagon₃ :
    (pullbackCompOfEq.{u} (Fc := Opens.map f.base) f.ringSheafOnOpensHom
          (frobeniusStageStructureMap X p hX n) (frobeniusColimitι Y p hY n ≫
            frobeniusColimitStructureSheafHom p f hX hY) rfl
          (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY
              n))).hom.app ((_root_.SheafOfModules.pullback.{u} g.ringSheafOnOpensHom).obj N) ≫
        (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) g.ringSheafOnOpensHom
          (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY)
          (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
          (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp' p f g hX hY hW
              n))).hom.app N =
      (_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n)).map
          ((pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) g.ringSheafOnOpensHom
              f.ringSheafOnOpensHom (f ≫ g).ringSheafOnOpensHom rfl HEq.rfl).hom.app N) ≫
          (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) (f ≫ g).ringSheafOnOpensHom
            (frobeniusStageStructureMap X p hX n) (frobeniusColimitι W p hW n ≫
              frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
            (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p (f ≫ g) hX hW
                n))).hom.app N :=
  pullbackCompOfEq_assoc_app.{u} (Fab := Opens.map (f ≫ g).base)
    (Gbc := Opens.map f.base) (Fabc := Opens.map (f ≫ g).base)
    g.ringSheafOnOpensHom f.ringSheafOnOpensHom (frobeniusStageStructureMap X p hX n)
        (f ≫ g).ringSheafOnOpensHom (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom
          p f hX hY) (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX
          hW) rfl rfl rfl rfl HEq.rfl (heq_of_eq
          (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY n))
        (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom_comp' p f g hX hY hW
            n)) (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p (f ≫ g) hX hW
            n)) N

/-- The three pentagons telescope. -/
lemma frobeniusStageExtendScalarsPullbackIso_comp_telescope :
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY)).map
        ((pullbackCompOfEq.{u} (Fc := Opens.map g.base) (frobeniusStageStructureMap W p hW n)
            (frobeniusColimitStructureSheafHom p g hY hW)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW) rfl
            HEq.rfl).hom.app N ≫ (pullbackCompOfEq.{u} (Fc := Opens.map g.base)
            g.ringSheafOnOpensHom (frobeniusStageStructureMap Y p hY n)
            (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p g hY hW) rfl
            (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p g hY hW
                n))).inv.app N) ≫
        ((pullbackCompOfEq.{u} (Fc := Opens.map f.base) (frobeniusStageStructureMap Y p hY n)
                (frobeniusColimitStructureSheafHom p f hX hY)
                (frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY) rfl
                HEq.rfl).hom.app ((_root_.SheafOfModules.pullback.{u} g.ringSheafOnOpensHom).obj
                N) ≫ (pullbackCompOfEq.{u} (Fc := Opens.map f.base) f.ringSheafOnOpensHom
                (frobeniusStageStructureMap X p hX n) (frobeniusColimitι Y p hY n ≫
                  frobeniusColimitStructureSheafHom p f hX hY) rfl
                (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hX hY
                    n))).inv.app ((_root_.SheafOfModules.pullback.{u} g.ringSheafOnOpensHom).obj
                N)) ≫ (_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n)).map
            ((pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) g.ringSheafOnOpensHom
                f.ringSheafOnOpensHom (f ≫ g).ringSheafOnOpensHom rfl HEq.rfl).hom.app N) =
      (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base)
            (frobeniusColimitStructureSheafHom p g hY hW)
            (frobeniusColimitStructureSheafHom p f hX hY)
            (frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
            (heq_of_eq (frobeniusColimitStructureSheafHom_comp p f g hX hY hW))).hom.app
          ((_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap W p hW n)).obj N) ≫
          ((pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base)
              (frobeniusStageStructureMap W p hW n) (frobeniusColimitStructureSheafHom p (f ≫ g) hX
                hW) (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW)
              rfl HEq.rfl).hom.app N ≫ (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) (f ≫
                g).ringSheafOnOpensHom (frobeniusStageStructureMap X p hX n)
              (frobeniusColimitι W p hW n ≫ frobeniusColimitStructureSheafHom p (f ≫ g) hX hW) rfl
              (heq_of_eq (frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p (f ≫ g) hX hW
                  n))).inv.app N) :=
  frobeniusStageExtendScalarsPullbackIso_comp_aux (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p f hX hY))
      (_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n))
    (frobeniusStageExtendScalarsPullbackIso_comp_pentagon₁ p f g hX hY hW n N)
    (frobeniusStageExtendScalarsPullbackIso_comp_pentagon₂ p f g hX hY hW n N)
    (frobeniusStageExtendScalarsPullbackIso_comp_pentagon₃ p f g hX hY hW n N)
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)

end CompPieces

/-- **The stage bridge is compatible with composition.**  For composable morphisms
`f : X ⟶ Y` and `g : Y ⟶ W` of schemes in characteristic `p`, the bridge of `g` carried along
the transition functor of `f`, followed by the bridge of `f` and the composition comparison of
the inverse images, is the composition comparison of the transition functors followed by the
bridge of `f ≫ g`: the family of stage bridges is a pseudonatural transformation. -/
theorem frobeniusStageExtendScalarsPullbackIso_comp (f : X ⟶ Y) (g : Y ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
    (n : ℕ) (N : _root_.SheafOfModules.{u} W.ringSheafOnOpens) :
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY)).map
        ((frobeniusStageExtendScalarsPullbackIso p g hY hW n).hom.app N) ≫
      (frobeniusStageExtendScalarsPullbackIso p f hX hY n).hom.app
          ((_root_.SheafOfModules.pullback.{u} g.ringSheafOnOpensHom).obj N) ≫
        (_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap X p hX n)).map
            ((_root_.SheafOfModules.pullbackComp.{u} g.ringSheafOnOpensHom
                f.ringSheafOnOpensHom).hom.app N) =
      (frobeniusColimitPullbackComp p f g hX hY hW).hom.app
          ((_root_.SheafOfModules.pullback.{u} (frobeniusStageStructureMap W p hW n)).obj N) ≫
        (frobeniusStageExtendScalarsPullbackIso p (f ≫ g) hX hW n).hom.app N := by
  have hKm : _root_.SheafOfModules.pullbackComp.{u} g.ringSheafOnOpensHom f.ringSheafOnOpensHom =
      (pullbackCompOfEq.{u} (Fc := Opens.map (f ≫ g).base) g.ringSheafOnOpensHom
        f.ringSheafOnOpensHom (f ≫ g).ringSheafOnOpensHom rfl HEq.rfl) :=
    (pullbackCompOfEq_self.{u} g.ringSheafOnOpensHom f.ringSheafOnOpensHom).symm
  rw [hKm, frobeniusStageExtendScalarsPullbackIso_hom_app_eq p (f ≫ g) hX hW n N,
    frobeniusStageExtendScalarsPullbackIso_hom_app_eq p g hY hW n N,
    frobeniusStageExtendScalarsPullbackIso_hom_app_eq p f hX hY n]
  exact frobeniusStageExtendScalarsPullbackIso_comp_telescope p f g hX hY hW n N

/-- **The stage functor's commutation with the transition functors is compatible with
composition**, on the finite locally free modules: for `g : X ⟶ Y` and `h : Y ⟶ W`, the
comparison `AlgebraicGeometry.frobeniusStageFunctorPullbackIso` of `g ≫ h` is the one of `h`
carried along the transition functor of `g`, followed by the one of `g`, conjugated by the
composition comparisons of the transition functors and of the restrictions of vector bundles.
This is `AlgebraicGeometry.frobeniusStageExtendScalarsPullbackIso_comp` on the full
subcategories. -/
theorem frobeniusStageFunctorPullbackIso_comp (g : X ⟶ Y) (h : Y ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
    (n : ℕ) (E : W.Vect) :
    (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hW).hom.app
          ((frobeniusStageFunctor W p hW n).obj E) ≫
        (frobeniusStageFunctorPullbackIso p (g ≫ h) hX hW n).hom.app E =
      (frobeniusColimitVectorBundlesPullback p g hX hY).map
          ((frobeniusStageFunctorPullbackIso p h hY hW n).hom.app E) ≫
        (frobeniusStageFunctorPullbackIso p g hX hY n).hom.app ((Scheme.Vect.pullback h).obj E) ≫
          (frobeniusStageFunctor X p hX n).map ((Scheme.Vect.pullbackComp g h).hom.app E) := by
  apply ObjectProperty.hom_ext
  exact (frobeniusStageExtendScalarsPullbackIso_comp p g h hX hY hW n E.obj).symm

end Comp

/-! ### The stage bridge at two equal morphisms -/

section Congr

variable (p : ℕ) [Fact p.Prime] {X E : Scheme.{u}}
  (hX : IsInCharacteristic X p) (hE : IsInCharacteristic E p)

/-- The bridge of [Stacks, Tag 0EXD] at two equal morphisms differs by the two transports along
the equality. -/
lemma frobeniusStageFunctorPullbackIso_congr {m m' : E ⟶ X} (h : m = m') (n : ℕ) (N : X.Vect) :
    (eqToIso (congrArg (fun m : E ⟶ X => frobeniusColimitVectorBundlesPullback p m hE hX)
        h)).hom.app ((frobeniusStageFunctor X p hX n).obj N) ≫
        (frobeniusStageFunctorPullbackIso p m' hE hX n).hom.app N =
      (frobeniusStageFunctorPullbackIso p m hE hX n).hom.app N ≫
        (frobeniusStageFunctor E p hE n).map ((Scheme.Vect.pullbackCongr h).hom.app N) := by
  subst h
  have h1 : (Scheme.Vect.pullbackCongr (rfl : m = m)).hom.app N = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    simp [Scheme.Modules.pullbackCongr]
  rw [h1]
  simp

end Congr

end AlgebraicGeometry

end
