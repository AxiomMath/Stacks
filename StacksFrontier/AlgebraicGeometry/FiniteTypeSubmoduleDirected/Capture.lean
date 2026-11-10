module

import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmoduleDirected.Extension
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.Image
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Capturing a finite type submodule of a pulled back module

Let `q : T ⟶ Y` be a morphism from a quasi-compact scheme to a quasi-compact quasi-separated
scheme, `F` an `𝒪_Y`-module, `K ⊆ F` a quasi-coherent submodule and `D ⊆ q^*F` a submodule of
finite type contained in the image of `q^*K`. Then some quasi-coherent submodule `N ⊆ K` of finite
type already has `D` inside the image of `q^*N`.

This is the module form of `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_of_le_comap`; it
is one of the two scheme inputs, the other being
`Stacks.FiniteTypeSubmodule.exists_isFiniteType_le_restrictTo_eq`, of the extension of finite
type quasi-coherent submodules compatibly with an étale chart on a quasi-compact quasi-separated
algebraic space (the module form of [Stacks, Tag 0829], proved along [Stacks, Tag 08GP]).

## Main definitions

* `Stacks.FiniteTypeSubmodule.monoOverDiagram`, `Stacks.FiniteTypeSubmodule.monoOverCocone`: the
  diagram of subobjects given by a monotone family of submodules, and its cocone with vertex the
  ambient module.

## Main results

* `Stacks.FiniteTypeSubmodule.iSup_subobjectMk_eq_top`: a family of submodules such that every
  section lies locally in one of them has supremum `⊤` as subobjects.
* `Stacks.FiniteTypeSubmodule.isColimitOfLocallyMem`: for a directed such family, the ambient
  module is the colimit of its members.
* `Stacks.FiniteTypeSubmodule.exists_forall_mem_of_isFiniteType`: if the ambient module is of
  finite type on a quasi-compact scheme, one member of such a directed family is everything
  ([Stacks, Tag 01BB]).
* `Stacks.FiniteTypeSubmodule.exists_local_lift_of_isColimit`: a section of a directed colimit
  of `𝒪_T`-modules lifts locally to a stage.
* `Stacks.FiniteTypeSubmodule.exists_isFiniteType_le_of_le_ofHom_pullback`: **the capture.**
* `Stacks.FiniteTypeSubmodule.exists_isFiniteType_ge_restrictTo_eq`: the extension from a
  quasi-compact open of a finite type quasi-coherent submodule, above a given one.

## Implementation notes

The quasi-coherent submodules of finite type of the module of `K` form a directed family whose
supremum is everything, by [Stacks, Tag 01PG] in its covering form
(`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section`), so `K` is their colimit
(`CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`). The pullback
`q^*` is a left adjoint, hence `q^*K` is the colimit of the `q^*N`, and a section of `q^*K` lifts
locally to one of the `q^*N`. So every section of `D` lies locally in the image of some `q^*N`;
the images form a directed family of submodules, and since `D` is of finite type on the
quasi-compact `T`, [Stacks, Tag 01BB] puts all of `D` inside one of them.

## References

* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict

universe u

namespace Stacks.FiniteTypeSubmodule

/-! ### Directed families of submodules -/

section Directed

variable {X : Scheme.{u}} {M : X.Modules}

/-- The inclusion of a submodule, as a morphism in the category `X.Modules` of `𝒪_X`-modules
(rather than in the category of sheaves of modules, which carries a separately declared
instance). -/
def inclusion (N : M.Submodule) : @Quiver.Hom X.Modules _ N.toSheafOfModules M :=
  N.ι

/-- The inclusion of a submodule in `X.Modules` is the inclusion `N.ι` of sheaves of modules. -/
theorem inclusion_eq (N : M.Submodule) : inclusion N = N.ι :=
  rfl

/-- The inclusion of a submodule is a monomorphism of `𝒪_X`-modules. -/
instance mono_inclusion (N : M.Submodule) : Mono (inclusion N) :=
  (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
    (inferInstanceAs (Mono N.toSubmodule.ι))

/-- The inclusion between two nested submodules, as a morphism in `X.Modules`. -/
def inclusionOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    @Quiver.Hom X.Modules _ N₁.toSheafOfModules N₂.toSheafOfModules :=
  SheafOfModules.Submodule.homOfLE h

/-- The inclusions of two nested submodules commute with the inclusion between them. -/
@[reassoc]
theorem inclusionOfLE_inclusion {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    inclusionOfLE h ≫ inclusion N₂ = inclusion N₁ :=
  SheafOfModules.Submodule.homOfLE_ι h

variable {I : Type u} [Preorder I]

/-- The diagram of subobjects of `M` given by a monotone family of submodules. -/
def monoOverDiagram (P : I → M.Submodule) (hP : Monotone P) : I ⥤ MonoOver M where
  obj i := MonoOver.mk (inclusion (P i))
  map {_ _} h := MonoOver.homMk (inclusionOfLE (hP h.le)) (inclusionOfLE_inclusion _)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The cocone of the diagram of a monotone family of submodules, with vertex `M` itself. -/
def monoOverCocone (P : I → M.Submodule) (hP : Monotone P) :
    Cocone (monoOverDiagram P hP ⋙ MonoOver.forget M) where
  pt := Over.mk (𝟙 M)
  ι :=
    { app := fun i => Over.homMk (inclusion (P i))
        (Category.comp_id _)
      naturality := fun _ _ h => Over.OverMorphism.ext
        ((inclusionOfLE_inclusion (hP h.le)).trans (Category.comp_id _).symm) }

omit [Preorder I] in
/-- **A family of submodules which locally contains every section has supremum `⊤`**, as
subobjects. The inclusion of the supremum is locally surjective, hence an epimorphism, hence an
isomorphism. -/
theorem iSup_subobjectMk_eq_top (P : I → M.Submodule)
    (hsup : ∀ (U : X.Opens) (s : Γ(M, U)), ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ i, M.presheaf.map (homOfLE hVU).op s ∈ (P i).obj (op V)) :
    (⨆ i, Subobject.mk (inclusion (P i))) = ⊤ := by
  classical
  let S : Subobject M := ⨆ i, Subobject.mk (inclusion (P i))
  let q : (S : X.Modules) ⟶ M := S.arrow
  let T := SheafOfModules.toSheaf X.ringCatSheaf
  let qSheaf := T.map q
  have hqSheaf : Epi qSheaf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi qSheaf).1
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨V, hVU, hxV, i, hi⟩ := hsup U t x hx
    let inj : @Quiver.Hom X.Modules _ (P i).toSheafOfModules (S : X.Modules) :=
      Subobject.ofMkLE _ S (le_iSup (fun i => Subobject.mk (inclusion (P i))) i)
    have hinj : inj ≫ q = inclusion (P i) := Subobject.ofMkLE_arrow _
    refine ⟨V, hVU, ⟨inj.app V ⟨_, hi⟩, ?_⟩, hxV⟩
    change ((inj ≫ q).app V) ⟨_, hi⟩ = M.presheaf.map (homOfLE hVU).op t
    rw [hinj]
    rfl
  have hq : Epi q := by
    refine ⟨fun {Z} g h hgh => ?_⟩
    have hmap : qSheaf ≫ T.map g = qSheaf ≫ T.map h := by
      change T.map q ≫ T.map g = T.map q ≫ T.map h
      exact (T.map_comp q g).symm.trans ((congrArg T.map hgh).trans (T.map_comp q h))
    exact T.map_injective ((cancel_epi qSheaf).1 hmap)
  have : IsIso q := isIso_of_mono_of_epi q
  simpa only [q, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso q

/-- **A directed family of submodules which locally contains every section has the ambient
module as its colimit.** This is
`CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup` together with
`Stacks.FiniteTypeSubmodule.iSup_subobjectMk_eq_top`. -/
def isColimitOfLocallyMem [IsDirectedOrder I] [Nonempty I] (P : I → M.Submodule)
    (hP : Monotone P)
    (hsup : ∀ (U : X.Opens) (s : Γ(M, U)), ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ i, M.presheaf.map (homOfLE hVU).op s ∈ (P i).obj (op V)) :
    IsColimit ((Over.forget M).mapCocone (monoOverCocone P hP)) := by
  have : Mono (monoOverCocone P hP).pt.hom := by
    change Mono (𝟙 M)
    infer_instance
  refine IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup (monoOverDiagram P hP)
    (monoOverCocone P hP) ?_
  change Subobject.mk (𝟙 M) =
    ⨆ i, Subobject.mk (inclusion (P i))
  rw [← Subobject.top_eq_id]
  exact (iSup_subobjectMk_eq_top P hsup).symm

/-- **[Stacks, Tag 01BB] for a directed family of submodules.** On a quasi-compact scheme, let
`M` be an `𝒪_X`-module of finite type and `P` a directed family of submodules such that every
section of `M` lies locally in one of them. Then one of them contains every section of `M`. -/
theorem exists_forall_mem_of_isFiniteType [CompactSpace X] [IsDirectedOrder I] [Nonempty I]
    (hM : M.IsFiniteType) (P : I → M.Submodule) (hP : Monotone P)
    (hsup : ∀ (U : X.Opens) (s : Γ(M, U)), ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ i, M.presheaf.map (homOfLE hVU).op s ∈ (P i).obj (op V)) :
    ∃ i, ∀ (U : X.Opens) (s : Γ(M, U)), s ∈ (P i).obj (op U) := by
  let Φ := (monoOverDiagram P hP ⋙ MonoOver.forget M) ⋙ Over.forget M
  have hc := isColimitOfLocallyMem P hP hsup
  let e := (colimit.isColimit Φ).coconePointUniqueUpToIso hc
  have hftcol : (colimit Φ).IsFiniteType := AlgebraicGeometry.isFiniteType_of_iso_modules e hM
  have hcpt : CompactSpace X.toPresheafedSpace := inferInstance
  obtain ⟨i, hi⟩ := @Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType
    X.toPresheafedSpace X.ringCatSheaf _ _ _ _ _ _ _ _ _ Φ hftcol
  have hfac : colimit.ι Φ i ≫ e.hom = (inclusion (P i)) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  have hepi : Epi (C := X.Modules) (colimit.ι Φ i) := hi
  have hepi' : Epi (inclusion (P i)) := by
    have := epi_comp' hepi (inferInstance : Epi e.hom)
    rwa [hfac] at this
  have hiso : IsIso (inclusion (P i)) := isIso_of_mono_of_epi _
  refine ⟨i, fun U s => ?_⟩
  obtain ⟨t, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective ((inclusion (P i)).app U)).1
    (Scheme.Modules.Hom.isIso_iff_isIso_app.1 hiso U)).2 s
  exact t.2

end Directed

/-! ### Lifting sections of a directed colimit -/

section Lift

variable {T : Scheme.{u}} {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **A section of a directed colimit of `𝒪_T`-modules lifts locally to a stage.** -/
theorem exists_local_lift_of_isColimit {Φ : I ⥤ T.Modules} {c : Cocone Φ} (hc : IsColimit c)
    {V : T.Opens} {x : T} (hx : x ∈ V) (s : Γ(c.pt, V)) :
    ∃ (W : T.Opens) (hWV : W ≤ V), x ∈ W ∧ ∃ (i : I) (t : Γ(Φ.obj i, W)),
      (c.ι.app i).app W t = c.pt.presheaf.map (homOfLE hWV).op s := by
  let e := (colimit.isColimit Φ).coconePointUniqueUpToIso hc
  obtain ⟨W, hWV, hxW, i, t, ht⟩ := @Stacks.SheafOfModules.exists_local_lift_from_stage
    T.toPresheafedSpace T.ringCatSheaf _ _ I _ _ _ Φ V x hx (e.inv.app V s)
  refine ⟨W, hWV, hxW, i, t, ?_⟩
  have hfac : colimit.ι Φ i ≫ e.hom = c.ι.app i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  have ht' : (colimit.ι Φ i).app W t =
      (colimit Φ).presheaf.map (homOfLE hWV).op (e.inv.app V s) := ht
  rw [← hfac]
  change e.hom.app W ((colimit.ι Φ i).app W t) = _
  rw [ht']
  refine (PresheafOfModules.naturality_apply e.hom.val (homOfLE hWV).op _).trans ?_
  change c.pt.presheaf.map (homOfLE hWV).op ((e.inv ≫ e.hom).app V s) = _
  rw [Iso.inv_hom_id]
  rfl

end Lift

/-! ### The capture -/

section Capture

variable {Y T : Scheme.{u}} {F : Y.Modules}

/-- The local image of a composite lies in the local image of the second map. -/
theorem ofHom_comp_le {A B G : T.Modules} (g : A ⟶ B) (f : B ⟶ G) :
    ofHom (g ≫ f) ≤ ofHom f := by
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ s hs
  refine (mem_ofHom_iff f s).2 fun x hx => ?_
  obtain ⟨V, hVU, hxV, t, ht⟩ := (mem_ofHom_iff (g ≫ f) s).1 hs x hx
  exact ⟨V, hVU, hxV, g.app V t, ht⟩

/-- The local image of the pullback of `a` lies in that of `b` when `a` factors through `b`. -/
private theorem ofHom_pullback_map_le_of_eq_comp {Y T : Scheme.{u}} (q : T ⟶ Y)
    {A B G : Y.Modules} (a : A ⟶ G) (b : B ⟶ G) (c : A ⟶ B) (h : a = c ≫ b) :
    ofHom ((Scheme.Modules.pullback q).map a) ≤ ofHom ((Scheme.Modules.pullback q).map b) := by
  rw [h, Functor.map_comp]
  exact ofHom_comp_le _ _

/-- A submodule whose subobject lies below a subobject `C` lies below the concrete submodule of
`C`. -/
theorem le_ofSubobject_of_mk_le {M : T.Modules} (N : M.Submodule) (C : Subobject M)
    (h : Subobject.mk (inclusion N) ≤ C) :
    N ≤ ofSubobject C := by
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ s hs
  refine le_obj_ofHom C.arrow U ⟨(Subobject.ofMkLE _ C h).app U ⟨s, hs⟩, ?_⟩
  exact congrArg (fun φ : @Quiver.Hom T.Modules _ N.toSheafOfModules M =>
    φ.app U (⟨s, hs⟩ : Γ(N.toSheafOfModules, U))) (Subobject.ofMkLE_arrow h)

/-- Quasi-coherence and finite type transfer along an isomorphism of `𝒪_X`-modules. -/
private theorem isQuasicoherent_and_isFiniteType_of_iso {X : Scheme.{u}} {A B : X.Modules}
    (e : A ≅ B) (h : A.IsQuasicoherent ∧ A.IsFiniteType) :
    B.IsQuasicoherent ∧ B.IsFiniteType :=
  ⟨Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso e h.1,
    AlgebraicGeometry.Modules.isFiniteType_of_iso e h.2⟩

/-- Two quasi-coherent submodules of finite type lie below a third one. -/
private theorem exists_isFiniteType_submodule_sup {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (A B : M.Submodule)
    (hA : (A.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (A.toSheafOfModules : X.Modules).IsFiniteType)
    (hB : (B.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (B.toSheafOfModules : X.Modules).IsFiniteType) :
    ∃ N : M.Submodule, ((N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType) ∧ A ≤ N ∧ B ≤ N := by
  obtain ⟨C, hCqc, hCft, hAC, hBC⟩ := exists_finiteTypeQuasicoherentSubobject_sup (F := M)
    (A := @Subobject.mk _ _ _ _ (inclusion A) (mono_inclusion A))
    (B := @Subobject.mk _ _ _ _ (inclusion B) (mono_inclusion B))
    (isQuasicoherent_and_isFiniteType_of_iso
      (@Subobject.underlyingIso _ _ _ _ (inclusion A) (mono_inclusion A)).symm hA).1
    (AlgebraicGeometry.isFiniteType_of_iso_modules
      (@Subobject.underlyingIso _ _ _ _ (inclusion A) (mono_inclusion A)) hA.2)
    (isQuasicoherent_and_isFiniteType_of_iso
      (@Subobject.underlyingIso _ _ _ _ (inclusion B) (mono_inclusion B)).symm hB).1
    (AlgebraicGeometry.isFiniteType_of_iso_modules
      (@Subobject.underlyingIso _ _ _ _ (inclusion B) (mono_inclusion B)) hB.2)
  exact ⟨ofSubobject C, isQuasicoherent_and_isFiniteType_of_iso (ofSubobjectIso C) ⟨hCqc, hCft⟩,
    le_ofSubobject_of_mk_le _ C hAC, le_ofSubobject_of_mk_le _ C hBC⟩

/-- A submodule of `K` which is quasi-coherent of finite type in `M`, read inside `K`, is again
quasi-coherent of finite type. -/
private theorem isQuasicoherent_and_isFiniteType_asSubmoduleOf {X : Scheme.{u}} {M : X.Modules}
    (K P : M.Submodule) (hPK : P ≤ K)
    (h : (P.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (P.toSheafOfModules : X.Modules).IsFiniteType) :
    ((asSubmoduleOf K P hPK).toSheafOfModules : X.Modules).IsQuasicoherent ∧
      ((asSubmoduleOf K P hPK).toSheafOfModules : X.Modules).IsFiniteType := by
  rw [← compose_asSubmoduleOf K P hPK] at h
  exact isQuasicoherent_and_isFiniteType_of_iso (composeIso _ _) h

/-- **Capturing a finite type submodule of a pulled back module.** Let `q : T ⟶ Y` be a morphism
from a quasi-compact scheme to a quasi-compact quasi-separated scheme, `F` an `𝒪_Y`-module, `K`
a quasi-coherent submodule of `F` and `D` a submodule of finite type of `q^*F` lying in the image
of `q^*K`. Then some quasi-coherent submodule `N ≤ K` of finite type has `D` in the image of
`q^*N`.

The module form of `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_of_le_comap`: `K` is the
directed colimit of its quasi-coherent submodules of finite type ([Stacks, Tag 01PG]), `q^*`
preserves it, and [Stacks, Tag 01BB] on `T` puts `D` inside one stage. -/
theorem exists_isFiniteType_le_of_le_ofHom_pullback [CompactSpace T] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (q : T ⟶ Y) (K : F.Submodule)
    (hK : (K.toSheafOfModules : Y.Modules).IsQuasicoherent)
    (D : ((Scheme.Modules.pullback q).obj F).Submodule)
    (hD : (D.toSheafOfModules : T.Modules).IsFiniteType)
    (hDK : D ≤ ofHom ((Scheme.Modules.pullback q).map
      (K.ι : (K.toSheafOfModules : Y.Modules) ⟶ F))) :
    ∃ N : F.Submodule, (N.toSheafOfModules : Y.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : Y.Modules).IsFiniteType ∧ N ≤ K ∧
      D ≤ ofHom ((Scheme.Modules.pullback q).map
        (N.ι : (N.toSheafOfModules : Y.Modules) ⟶ F)) := by
  classical
  let Km : Y.Modules := K.toSheafOfModules
  have : Km.IsQuasicoherent := hK
  let I := {N : Km.Submodule // (N.toSheafOfModules : Y.Modules).IsQuasicoherent ∧
    (N.toSheafOfModules : Y.Modules).IsFiniteType}
  have hdir : IsDirectedOrder I := ⟨fun a b => by
    obtain ⟨N, hN, haN, hbN⟩ := exists_isFiniteType_submodule_sup a.1 b.1 a.2 b.2
    exact ⟨⟨N, hN⟩, haN, hbN⟩⟩
  have : Nonempty I := by
    obtain ⟨G, hGqc, hGft, -⟩ := exists_finiteTypeQuasicoherentSubobject_section Km ⊤
      (by rw [Opens.coe_top]; exact isCompact_univ) 0
    exact ⟨⟨ofSubobject G, isQuasicoherent_and_isFiniteType_of_iso (ofSubobjectIso G)
      ⟨hGqc, hGft⟩⟩⟩
  -- every section of `K` lies locally in a member of the family (Tag 01PG)
  have hsupK : ∀ (U : Y.Opens) (s : Γ(Km, U)), ∀ x ∈ U, ∃ (V : Y.Opens) (hVU : V ≤ U),
      x ∈ V ∧ ∃ i : I, Km.presheaf.map (homOfLE hVU).op s ∈ i.1.obj (op V) := by
    intro U s x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    have hWle : W ≤ U := fun y hy => hWU hy
    obtain ⟨G, hGqc, hGft, tG, htG⟩ := exists_finiteTypeQuasicoherentSubobject_section Km W
      hW.isCompact (Km.presheaf.map (homOfLE hWle).op s)
    exact ⟨W, hWle, hxW, ⟨ofSubobject G, isQuasicoherent_and_isFiniteType_of_iso
      (ofSubobjectIso G) ⟨hGqc, hGft⟩⟩,
      le_obj_ofHom G.arrow W ⟨tG, htG⟩⟩
  have hmono : Monotone (fun i : I => i.1) := fun _ _ h => h
  have hc := isColimitOfLocallyMem (fun i : I => i.1) hmono hsupK
  have hcq := isColimitOfPreserves (Scheme.Modules.pullback q) hc
  -- the images of the pulled back members
  let P' : I → ((Scheme.Modules.pullback q).obj F).Submodule := fun i =>
    ofHom ((Scheme.Modules.pullback q).map (inclusion i.1 ≫ inclusion K))
  have hP' : Monotone P' := by
    intro i j hij
    exact ofHom_pullback_map_le_of_eq_comp q _ _ (inclusionOfLE (show i.1 ≤ j.1 from hij))
      (Scheme.Modules.hom_ext _ _ fun U => by ext x; rfl)
  let Ds : T.Modules := D.toSheafOfModules
  let P'' : I → Ds.Submodule := fun i => asSubmoduleOf D (D ⊓ P' i) inf_le_left
  have hP'' : Monotone P'' := by
    intro i j hij
    refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
    intro U s hs
    exact ⟨hs.1, PresheafOfModules.Submodule.le_iff.1
      (SheafOfModules.Submodule.le_iff.1 (hP' hij)) U hs.2⟩
  -- every section of `D` lies locally in one of the images
  have hsupD : ∀ (U : T.Opens) (s : Γ(Ds, U)), ∀ x ∈ U, ∃ (V : T.Opens) (hVU : V ≤ U),
      x ∈ V ∧ ∃ i : I, Ds.presheaf.map (homOfLE hVU).op s ∈ (P'' i).obj (op V) := by
    intro U s x hx
    have hs : s.1 ∈ (ofHom ((Scheme.Modules.pullback q).map
        ((inclusion K)))).obj (op U) :=
      PresheafOfModules.Submodule.le_iff.1 (SheafOfModules.Submodule.le_iff.1 hDK) (op U) s.2
    obtain ⟨V₀, hV₀U, hxV₀, t, ht⟩ := (mem_ofHom_iff _ _).1 hs x hx
    obtain ⟨W, hWV₀, hxW, i, t', ht'⟩ := exists_local_lift_of_isColimit hcq hxV₀ t
    refine ⟨W, hWV₀.trans hV₀U, hxW, i, ?_⟩
    refine ⟨D.map_mem _ s.2, le_obj_ofHom _ W ⟨t', ?_⟩⟩
    have ht'' : ((Scheme.Modules.pullback q).map
        (inclusion i.1)).app W t' =
        ((Scheme.Modules.pullback q).obj Km).presheaf.map (homOfLE hWV₀).op t := ht'
    have key : ((Scheme.Modules.pullback q).map (inclusion i.1) ≫
        (Scheme.Modules.pullback q).map (inclusion K)).app W t' =
        ((Scheme.Modules.pullback q).obj F).presheaf.map (homOfLE (hWV₀.trans hV₀U)).op s.1 := by
      change ((Scheme.Modules.pullback q).map (inclusion K)).app W
        (((Scheme.Modules.pullback q).map (inclusion i.1)).app W t') = _
      rw [ht'']
      refine (PresheafOfModules.naturality_apply
        ((Scheme.Modules.pullback q).map (inclusion K)).val (homOfLE hWV₀).op t).trans ?_
      change ((Scheme.Modules.pullback q).obj F).presheaf.map (homOfLE hWV₀).op
        (((Scheme.Modules.pullback q).map (inclusion K)).app V₀ t) = _
      rw [ht]
      change _ = (((Scheme.Modules.pullback q).obj F).presheaf.map
        ((homOfLE hV₀U).op ≫ (homOfLE hWV₀).op)) s.1
      rw [Functor.map_comp]
      rfl
    exact (congrArg (fun φ => Scheme.Modules.Hom.app φ W t')
      ((Scheme.Modules.pullback q).map_comp (inclusion i.1) (inclusion K))).trans key
  obtain ⟨i, hi⟩ := exists_forall_mem_of_isFiniteType hD P'' hP'' hsupD
  have hDP' : D ≤ P' i := by
    refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
    rintro ⟨U⟩ s hs
    exact (hi U ⟨s, hs⟩).2
  have hN := isQuasicoherent_and_isFiniteType_of_iso (composeIso K i.1).symm i.2
  refine ⟨compose K i.1, hN.1, hN.2,
    compose_le K i.1, hDP'.trans ?_⟩
  let α : @Quiver.Hom Y.Modules _ i.1.toSheafOfModules (compose K i.1).toSheafOfModules :=
    (composeIso K i.1).inv
  have he : inclusion i.1 ≫ inclusion K = α ≫ inclusion (compose K i.1) :=
    ((Iso.inv_comp_eq _).2 (composeIso_hom_ι K i.1).symm).symm
  exact ofHom_pullback_map_le_of_eq_comp q _ _ α he

end Capture

/-! ### Extending from a quasi-compact open above a given submodule -/

section Enlarge

variable {X : Scheme.{u}} {F : X.Modules}

/-- The concrete submodule of a subobject lying below the subobject of a submodule `N` lies
below `N`. -/
theorem ofSubobject_le_of_le_mk (P : Subobject F) (N : F.Submodule)
    (h : P ≤ Subobject.mk (inclusion N)) : ofSubobject P ≤ N := by
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ s hs
  obtain ⟨t, rfl⟩ := (obj_ofHom_of_mono P.arrow U).le hs
  let g : @Quiver.Hom X.Modules _ (P : X.Modules) N.toSheafOfModules :=
    Subobject.ofLE P _ h ≫ (Subobject.underlyingIso (inclusion N)).hom
  have hg : g ≫ inclusion N = P.arrow := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun φ => Subobject.ofLE P _ h ≫ φ)
      (Subobject.underlyingIso_hom_comp_eq_mk (inclusion N))).trans ?_
    exact Subobject.ofLE_arrow h
  have key : (g ≫ inclusion N).app U t = P.arrow.app U t :=
    congrArg (fun φ : @Quiver.Hom X.Modules _ (P : X.Modules) F => φ.app U t) hg
  have h2 : (g ≫ inclusion N).app U t ∈ N.obj (op U) := (g.app U t).2
  rwa [key] at h2

/-- A submodule `P ≤ K` whose reading inside `K` lies below `G` lies below `compose K G`. -/
theorem le_compose_of_asSubmoduleOf_le (K P : F.Submodule) (hPK : P ≤ K)
    (G : (K.toSheafOfModules : X.Modules).Submodule) (h : asSubmoduleOf K P hPK ≤ G) :
    P ≤ compose K G := by
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  intro V s hs
  exact (mem_compose_iff K G V s).2
    ⟨PresheafOfModules.Submodule.le_iff.1 (SheafOfModules.Submodule.le_iff.1 hPK) V hs,
      PresheafOfModules.Submodule.le_iff.1 (SheafOfModules.Submodule.le_iff.1 h) V hs⟩

/-- **Extension of a finite type quasi-coherent submodule from a quasi-compact open, above a
given one.** On a quasi-compact quasi-separated scheme `X`, let `F` be a quasi-coherent
`𝒪_X`-module, `U` a quasi-compact open, `D` a quasi-coherent submodule of finite type of `F|_U`
and `C` a quasi-coherent submodule of finite type of `F` with `C|_U ≤ D`. Then some
quasi-coherent submodule `N` of finite type of `F` contains `C` and restricts to exactly `D` on
`U`.

[Stacks, Tag 01PF] extends `D` to some `N₁`; the join `S` of `N₁` and `C` is quasi-coherent and
restricts into `D`, and a common finite type quasi-coherent bound of `N₁` and `C` inside `S`
([Stacks, Tag 01PG], `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_sup`) is `N`.
This is the affine step of the extension of finite type quasi-coherent submodules along
[Stacks, Tag 08GP]: there `D` is the restriction of the extension already found over the open
member of the square, and `C` captures the chart over the affine member. -/
@[ega "I 9.4.3" "special case", ega "I 9.4.7" "more general"]
theorem exists_isFiniteType_ge_restrictTo_eq [CompactSpace X] [QuasiSeparatedSpace X]
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsCompact (U : Set X))
    (D : (F.restrict U.ι).Submodule)
    (hDqc : (D.toSheafOfModules : U.toScheme.Modules).IsQuasicoherent)
    (hDft : (D.toSheafOfModules : U.toScheme.Modules).IsFiniteType)
    (C : F.Submodule) (hCqc : (C.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hCft : (C.toSheafOfModules : X.Modules).IsFiniteType) (hCD : restrictTo U.ι C ≤ D) :
    ∃ N : F.Submodule, (N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType ∧ C ≤ N ∧ restrictTo U.ι N = D := by
  classical
  obtain ⟨N₁, hN₁qc, hN₁ft, hN₁⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_isFiniteType_submodule_restrictTo_eq_of_qcqs
      hU D hDqc hDft
  let S : Subobject F := Subobject.mk (inclusion N₁) ⊔ Subobject.mk (inclusion C)
  have hSqc : (S : X.Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.Crystals.isQuasicoherent_sup _ _
      (Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso
        (Subobject.underlyingIso (inclusion N₁)).symm hN₁qc)
      (Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso
        (Subobject.underlyingIso (inclusion C)).symm hCqc)
  let K : F.Submodule := ofSubobject S
  have hKqc : (K.toSheafOfModules : X.Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso
      (ofSubobjectIso S) hSqc
  have hN₁K : N₁ ≤ K := le_ofSubobject_of_mk_le N₁ S le_sup_left
  have hCK : C ≤ K := le_ofSubobject_of_mk_le C S le_sup_right
  have hKD : K ≤ coRestrict U.ι D := by
    refine ofSubobject_le_of_le_mk S _ (sup_le ?_ ?_)
    · exact Subobject.mk_le_mk_of_comm
        (inclusionOfLE ((le_coRestrict_iff U.ι N₁ D).2 hN₁.le)) (inclusionOfLE_inclusion _)
    · exact Subobject.mk_le_mk_of_comm
        (inclusionOfLE ((le_coRestrict_iff U.ι C D).2 hCD)) (inclusionOfLE_inclusion _)
  let Km : X.Modules := K.toSheafOfModules
  have : Km.IsQuasicoherent := hKqc
  let a₁ := asSubmoduleOf K N₁ hN₁K
  let c₁ := asSubmoduleOf K C hCK
  obtain ⟨G, hG, haG, hcG⟩ := exists_isFiniteType_submodule_sup (M := Km) a₁ c₁
    (isQuasicoherent_and_isFiniteType_asSubmoduleOf K N₁ hN₁K ⟨hN₁qc, hN₁ft⟩)
    (isQuasicoherent_and_isFiniteType_asSubmoduleOf K C hCK ⟨hCqc, hCft⟩)
  have hN₁N : N₁ ≤ compose K G := le_compose_of_asSubmoduleOf_le K N₁ hN₁K G haG
  have hN := isQuasicoherent_and_isFiniteType_of_iso (composeIso K G).symm hG
  refine ⟨compose K G, hN.1, hN.2, le_compose_of_asSubmoduleOf_le K C hCK G hcG, ?_⟩
  refine le_antisymm ((le_coRestrict_iff U.ι _ D).1 ((compose_le K G).trans hKD)) ?_
  rw [← hN₁]
  exact restrictTo_mono U.ι hN₁N

end Enlarge

end Stacks.FiniteTypeSubmodule

end
