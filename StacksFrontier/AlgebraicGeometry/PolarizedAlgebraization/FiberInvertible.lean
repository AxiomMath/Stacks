module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.FiberIso
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE

/-!
# Invertibility from a closed subscheme of the base

Let `f : X ⟶ S` be proper, `i : S₀ ⟶ S` a closed immersion through which every closed point of
`S` factors, and `X₀ = X ×_S S₀`. A finitely presented `𝒪_X`-module `ℱ`, flat over `S`, whose
restriction to `X₀` is invertible is invertible: on the fibres over the closed points of `S` it is
invertible, so by [Stacks, Tag 080Q] it is free of rank one near every point over a closed point
of `S`, and every point of `X` specializes to such a point because `f` is closed.

## Main results

* `Stacks.PolarizedAlgebraization.exists_mem_over_isoUnit_of_fiber`: [Stacks, Tag 080Q] in rank
  one — a finitely presented module, flat over the base at a point, whose restriction to the fibre
  is invertible, is trivial near that point.
* `Stacks.PolarizedAlgebraization.isInvertibleModule_of_isPullback`, over a quasi-compact base
  (over a base with no closed points the statement fails).

## References

* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample (IsAmple IsInvertibleModule)

universe u

namespace Stacks.PolarizedAlgebraization

/-! ### Trivializations on the slice site and on the open subscheme -/

/-- The free module on an open `U`, read through the equivalence between sheaves of modules over
the restricted structure sheaf and sheaves of modules on `U` as a scheme. -/
def overEquivFreeIso {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let G := (Scheme.Modules.overEquiv U).functor
  haveI : PreservesColimitsOfShape.{u, u} (Discrete I) G :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} G
  exact @_root_.SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ G I this (Iso.refl _)

/-- **A trivialization on the slice site over `U` is a trivialization of the restriction to
`U`.** -/
def restrictIsoFreeOfOverIsoFree {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : M.over U ≅ _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I) :
    M.restrict U.ι ≅ _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫ (overEquivFreeIso U I).symm

/-! ### The pointwise statement -/

/-- Finite local freeness of rank `r` transfers from `E` to any module isomorphic to a pullback
of `E`. -/
private theorem isFiniteLocallyFreeOfRank_of_iso_pullback {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (E : Z.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    {G : Y.Modules} (e : (Scheme.Modules.pullback g).obj E ≅ G) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r)

/-- **Stacks Tag 080Q, rank one.** Let `f : X ⟶ S` be of finite presentation and `ℱ` a finitely
presented `𝒪_X`-module, flat over `S` at `x`, whose restriction to the fibre through `x` is finite
locally free of rank one. Then `ℱ` is trivial on a neighbourhood of `x`.

Tag 080Q makes `ℱ` free of some finite rank `n` on a neighbourhood `U` of `x`, the stalk of the
fibre module being free; pulling that trivialization back to the trace of `U` on the fibre, which
contains the point of the fibre over `x`, the fibre module is free of both ranks `n` and `1`
there, so `n = 1`. -/
theorem exists_mem_over_isoUnit_of_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : _root_.AlgebraicGeometry.FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (x : X) (hflat : AlgebraicGeometry.IsFlatOverAt (Scheme.Hom.toLRSHom f).toShHom F x)
    (hfib : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) 1) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (F.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  have hfiber :
      let := Stacks.Flatness.stalkModule
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x)
      Module.Flat (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x))) := by
    obtain ⟨q, hq, -⟩ := hfib.exists_isFiniteLocallyFreeOfRankData
    have hfree := Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFreeData_stalkFree
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) q hq (f.asFiber x)
    exact @Module.Flat.of_free _ _ _ _ _ hfree
  obtain ⟨U, hxU, n, ⟨e⟩⟩ :=
    Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk f hf F x hflat hfiber
  let V : (f.fiber (f x)).Opens := (f.fiberι (f x)) ⁻¹ᵁ U
  have hxV : f.asFiber x ∈ V := by
    change (f.fiberι (f x)) (f.asFiber x) ∈ U
    rwa [f.fiberι_asFiber]
  have hU : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) n :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm ≪≫
        restrictIsoFreeOfOverIsoFree F U _ e).symm
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv _ n Equiv.ulift)
  have hn := isFiniteLocallyFreeOfRank_of_iso_pullback (f.fiberι (f x) ∣_ U)
    ((Scheme.Modules.pullback U.ι).obj F) n
    ((Scheme.Modules.pullbackComp _ U.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι _ U)).app F ≪≫
        ((Scheme.Modules.pullbackComp V.ι (f.fiberι (f x))).app F).symm)
  have hn1 : n = 1 := Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ hn
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback V.ι
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) 1) ⟨_, hxV⟩
  subst hn1
  exact ⟨U, hxU, ⟨e ≪≫ Stacks.SheafOfModules.Invertible.freeUniqueIso _⟩⟩

/-! ### Fibres over the closed subscheme -/

variable {X S X₀ S₀ : Scheme.{u}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {j : X₀ ⟶ X} {i : S₀ ⟶ S}

/-- **The restriction of `ℱ` to the fibre of `X` over a point of `S₀` is free of rank one** when
the restriction of `ℱ` to `X₀ = X ×_S S₀` is: the fibre of `X` over `i s₀` is the fibre of `X₀`
over `s₀` (`Stacks.PolarizedAlgebraization.fiberIsoOfIsPullback`). -/
theorem isFiniteLocallyFreeOfRank_one_pullback_fiberι (h : IsPullback j f₀ f i)
    [IsClosedImmersion i] (s₀ : S₀) (F : X.Modules) (L₀ : X₀.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L₀ 1]
    (e : (Scheme.Modules.pullback j).obj F ≅ L₀) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (f.fiberι (i s₀))).obj F) 1 := by
  let φ := fiberIsoOfIsPullback h s₀
  let G := (Scheme.Modules.pullback (f.fiberι (i s₀))).obj F
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback φ.hom).obj G) 1 :=
    isFiniteLocallyFreeOfRank_of_iso_pullback (f₀.fiberι s₀) L₀ 1
      (((Scheme.Modules.pullback (f₀.fiberι s₀)).mapIso e).symm ≪≫
        (Scheme.Modules.pullbackComp (f₀.fiberι s₀) j).app F ≪≫
          (Scheme.Modules.pullbackCongr (fiberIsoOfIsPullback_hom_fiberι h s₀).symm).app F ≪≫
            ((Scheme.Modules.pullbackComp φ.hom (f.fiberι (i s₀))).app F).symm)
  exact isFiniteLocallyFreeOfRank_of_iso_pullback φ.inv _ 1
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr φ.inv_hom_id).app _ ≪≫ (Scheme.Modules.pullbackId _).app _)

/-! ### The global statement -/

/-- **A finitely presented module, flat over the base, whose restriction to the part of `X` over
a closed subscheme of the base containing every closed point is invertible, is invertible.** -/
theorem isInvertibleModule_of_isPullback (h : IsPullback j f₀ f i) [IsClosedImmersion i]
    (hcl : ∀ s : S, IsClosed ({s} : Set S) → s ∈ Set.range i)
    [IsProper f] [CompactSpace S] (hfp : _root_.AlgebraicGeometry.FinitePresentation f)
    (F : X.Modules) [F.IsFinitePresentation]
    (hflat : AlgebraicGeometry.IsFlatOver (Scheme.Hom.toLRSHom f).toShHom F)
    (L₀ : X₀.Modules) [IsInvertibleModule X₀ L₀]
    (e : (Scheme.Modules.pullback j).obj F ≅ L₀) :
    IsInvertibleModule X F := by
  have := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X₀ L₀
  have hloc : ∀ x : X, IsClosed ({f x} : Set S) → ∃ U : X.Opens, x ∈ U ∧
      Nonempty (F.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
    intro x hx
    obtain ⟨s₀, hs₀⟩ := hcl _ hx
    have hfib := isFiniteLocallyFreeOfRank_one_pullback_fiberι h s₀ F L₀ e
    rw [hs₀] at hfib
    exact exists_mem_over_isoUnit_of_fiber f hfp F x (hflat x) hfib
  refine Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over X F
    fun x => ?_
  have hC : IsClosed (f '' closure ({x} : Set X)) := f.isClosedMap _ isClosed_closure
  obtain ⟨s, ⟨x₁, hx₁, rfl⟩, hs⟩ :=
    hC.exists_closed_singleton ⟨f x, x, subset_closure rfl, rfl⟩
  obtain ⟨U, hU, he⟩ := hloc x₁ hs
  exact ⟨U, (specializes_iff_mem_closure.mpr hx₁).mem_open U.isOpen hU, he⟩

end Stacks.PolarizedAlgebraization

end
