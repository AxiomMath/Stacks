module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CokernelComp
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# Facts about finite locally free and invertible modules on a scheme

This file collects, in one spelling, the statements about modules on a scheme that the
inductive step of Stacks Tag 02UI consumes.

* An extension of finite locally free modules of constant ranks `a` and `c` is finite locally free
  of constant rank `a + c`. An epimorphism onto a finite locally free module splits near every
  point, so near every point the middle term is a biproduct of the outer two, hence finite
  locally free; it is then of some constant rank near every point, and additivity of the rank
  along the restricted sequence pins that rank to `a + c`.
* A module is invertible exactly when it is finite locally free of rank one (Tag 0B8M on a
  scheme).
* Pullback preserves constant rank and invertibility, and flat pullback preserves short exactness.

## Main results

* `Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact`
* `Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact`
* `Stacks.Chow.GenuineChern.exists_shortExact_pair`
* `Stacks.Chow.GenuineChern.isInvertible_iff_isFiniteLocallyFreeOfRank_one`
* `Stacks.Chow.GenuineChern.isInvertible_pullback`
* `Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_pullback`
* `Stacks.Chow.GenuineChern.shortExact_map_pullback`

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}}

/-- A family of opens with `x ∈ U x` for every point `x` covers the scheme. -/
private theorem iSup_eq_top_of_mem (U : X → X.Opens) (hU : ∀ x, x ∈ U x) : iSup U = ⊤ :=
  eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hU y⟩

/-- Restricting a finite locally free module to an open gives a finite locally free module. -/
private theorem isFiniteLocallyFree_restrict {M : X.Modules}
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) (V : X.Opens) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.restrictFunctor V.ι).obj M) :=
  (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (((Scheme.Modules.isFiniteLocallyFree_iff _).mpr h).restrict V.ι)

/-- Restricting a module of constant rank `r` to an open gives a module of constant rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_restrict {M : X.Modules} {r : ℕ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) (V : X.Opens) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor V.ι).obj M) r :=
  (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
    (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr h).restrict V.ι)

/-- **The middle term of an extension of finite locally free modules is finite locally free.**
The epimorphism onto the third term splits near every point; there the middle term is the
biproduct of the restricted outer terms. -/
theorem isFiniteLocallyFree_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁)
    (h₃ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂ := by
  have := hS.epi_g
  have := h₃
  choose V hyV hsplit using fun y : X ↦ exists_isSplitEpi_restrictFunctor_map S.g y
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mp ?_
  refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top V
    (iSup_eq_top_of_mem V hyV) fun y ↦ ?_
  · let G := Scheme.Modules.restrictFunctor (V y).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have := hsplit y
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (S.map G).X₁ :=
      isFiniteLocallyFree_restrict h₁ (V y)
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (S.map G).X₃ :=
      isFiniteLocallyFree_restrict h₃ (V y)
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((S.map G).X₁ ⊞ (S.map G).X₃ : (V y).toScheme.Modules) :=
      SheafOfModules.isFiniteLocallyFree_biprod _ _
    exact (Scheme.Modules.isFiniteLocallyFree_iff _).mpr <|
      SheafOfModules.IsFiniteLocallyFree.of_iso (ShortComplex.Splitting.ofExactOfSection (S.map G)
        hS'.exact (section_ (G.map S.g)) (IsSplitEpi.id _) hS'.mono_f).isoBinaryBiproduct.symm

/-- **An extension of finite locally free modules of constant ranks `a` and `c` is finite
locally free of constant rank `a + c`.** -/
theorem isFiniteLocallyFreeOfRank_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (a c : ℕ)
    (h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ a)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (a + c) := by
  have hfl : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂ :=
    isFiniteLocallyFree_of_shortExact S hS
      (have := h₁; SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree S.X₁ a)
      (have := h₃; SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree S.X₃ c)
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₂ hfl x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ (a + c)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U
    (iSup_eq_top_of_mem U hx) fun x ↦ ?_
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁ a :=
      isFiniteLocallyFreeOfRank_restrict h₁ (U x)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ c :=
      isFiniteLocallyFreeOfRank_restrict h₃ (U x)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ (r x) := hr x
    have hrx : r x = a + c :=
      SheafOfModules.rank_add_of_shortExact (S.map G) hS' a (r x) c (⟨x, hx x⟩ : (U x).toScheme)
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hrx ▸ hr x)

/-- **The two short exact sequences of the 02UI step** for modules on a scheme: given
`S₁ : 0 ⟶ F ⟶ A ⟶ L ⟶ 0`, `S₂ : 0 ⟶ A' ⟶ B ⟶ C ⟶ 0` short exact and `A ≅ A'`, there are
short exact sequences `0 ⟶ F ⟶ B ⟶ Q ⟶ 0` and `0 ⟶ L ⟶ Q ⟶ C ⟶ 0`. This is
`Stacks.Chow.GenuineChern.exists_shortExact_pair_abelian`, whose maps are the composite
`F ⟶ B`, its cokernel and the maps induced on cokernels. -/
theorem exists_shortExact_pair (S₁ S₂ : ShortComplex X.Modules) (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (e : S₁.X₂ ≅ S₂.X₁) :
    ∃ T₂ T₃ : ShortComplex X.Modules, T₂.ShortExact ∧ T₃.ShortExact ∧
      Nonempty (T₂.X₁ ≅ S₁.X₁) ∧ Nonempty (T₂.X₂ ≅ S₂.X₂) ∧ Nonempty (T₂.X₃ ≅ T₃.X₂) ∧
      Nonempty (T₃.X₁ ≅ S₁.X₃) ∧ Nonempty (T₃.X₃ ≅ S₂.X₃) :=
  exists_shortExact_pair_abelian S₁ S₂ h₁ h₂ e

/-! ### Invertible modules -/

/-- **Stacks Tag 0B8M on a scheme**: a module is invertible exactly when it is finite locally
free of rank one. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one (L : X.Modules) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X L

/-- A finite locally free module of rank one is invertible. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mpr inferInstance

/-- An invertible module is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  (isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mp inferInstance

/-! ### Pullback -/

/-- The pullback of an invertible module along any morphism of schemes is invertible. -/
theorem isInvertible_pullback {Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.WeilCohomology.isInvertible_pullback_obj f L hL

/-- The pullback of a finite locally free module of constant rank `r` along any morphism of
schemes is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_pullback {Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ((Scheme.Modules.pullback f).obj E) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f E r

/-- Pullback along a flat morphism of schemes preserves short exact sequences of modules. -/
theorem shortExact_map_pullback {Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  Stacks.WeilCohomology.shortExact_map_pullback f S hS

end Stacks.Chow.GenuineChern
