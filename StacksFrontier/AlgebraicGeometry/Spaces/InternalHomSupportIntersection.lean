module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties

/-!
# The support of the internal Hom of two modules on an algebraic space

Let `X` be an algebraic space and `M`, `N` two `𝒪_X`-modules of finite type.  The support of the
internal Hom `𝓗om_{𝒪_X}(M, N)` (at the module universe of the schemes,
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall`) lies in `Supp M ∩ Supp N`: where the stalk
of `M` (or `N`) vanishes, the module vanishes on an étale neighbourhood
(`AlgebraicGeometry.Space.exists_zero_neighborhood_of_isFiniteTypeOnSite`), and a section of the
internal Hom over a chart on which `M` (or `N`) vanishes is a morphism of modules on the slice
with zero source (or target), hence zero.  Consequently, for coherent `M`, `N` with
`Supp M ∩ Supp N` proper over the base, `𝓗om(M, N)` has proper support.  This is the step of the
proof of Stacks 08B9 that bounds the scheme-theoretic support of `𝓗om(M, N)`.

## Main results

* `AlgebraicGeometry.Space.subsingleton_smallEtaleInternalHomSmall_obj` — the sections of
  `𝓗om(M, N)` over a chart vanish when `M` or `N` vanishes on every chart over it.
* `AlgebraicGeometry.Space.supportOfSheaf_smallEtaleInternalHomSmall_subset_inter` —
  `Supp 𝓗om(M, N) ⊆ Supp M ∩ Supp N`.
* `AlgebraicGeometry.Space.hasProperSupport_smallEtaleInternalHomSmall` — `𝓗om(M, N)` has proper
  support when `Supp M ∩ Supp N` is proper over the base.

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The sections of `𝓗om(M, N)` over a chart `U` vanish when `M`, or `N`, has vanishing sections
over every chart mapping to `U`: such a section is a morphism of modules on the slice over `U`,
with zero source or zero target. -/
theorem subsingleton_smallEtaleInternalHomSmall_obj (M N : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1)
    (h : (∀ (V : SmallEtale B S hS X.1) (_ : V ⟶ U), Subsingleton (M.val.obj (op V))) ∨
      (∀ (V : SmallEtale B S hS X.1) (_ : V ⟶ U), Subsingleton (N.val.obj (op V)))) :
    Subsingleton ((smallEtaleInternalHomSmall B S hS X.1 X.2 M N).val.obj (op U)) := by
  let R := smallEtaleRingedSite B S hS X.1 X.2
  have hT : Subsingleton ((_root_.internalHom R.O.obj (RingedSite.valOf R M)
      (RingedSite.valOf R N)).obj (op U)) := by
    refine ⟨fun α β => ?_⟩
    refine PresheafOfModules.hom_ext fun V => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rcases h with hM | hN
    · have : Subsingleton (M.val.obj (op V.unop.left)) := hM V.unop.left V.unop.hom
      have hx : x = 0 := Subsingleton.elim (α := M.val.obj (op V.unop.left)) x 0
      rw [hx, map_zero, map_zero]
    · have : Subsingleton (N.val.obj (op V.unop.left)) := hN V.unop.left V.unop.hom
      exact Subsingleton.elim (α := N.val.obj (op V.unop.left)) _ _
  exact ((equivShrink _).symm : Shrink.{u} ((_root_.internalHom R.O.obj (RingedSite.valOf R M)
      (RingedSite.valOf R N)).obj (op U)) ≃ _).subsingleton

/-- A module whose sections vanish over every chart refining a neighbourhood of a geometric
point has vanishing stalk there. -/
theorem subsingleton_stalkSet_of_forall_subsingleton (K : Modules.{u, u} B S hS X.1 X.2)
    {p : GeometricPoint B S hS X.1} (U : SmallEtaleNeighborhood p)
    (hU : ∀ (V : SmallEtale B S hS X.1) (_ : V ⟶ U.chart), Subsingleton (K.val.obj (op V))) :
    Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj K).obj ⋙ forget AddCommGrpCat)) := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 p
  refine (subsingleton_stalkSet_iff B S hS X.1 X.2 _ p).2 fun N σ => ?_
  obtain ⟨L, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs N U
  have hsub : Subsingleton (K.val.obj (op L.chart)) := hU L.chart g.hom
  have hz : ((SheafOfModules.toSheaf _).obj K).obj.map f.hom.op σ = 0 :=
    Subsingleton.elim (α := K.val.obj (op L.chart)) _ _
  have hm := (largestOpenZeroLocus_restrict_iff B S hS X.1 _ N.chart σ L.chart f.hom).mp hz
    (neighborhoodPoint B S hS X.1 L).image
  rwa [neighborhoodPoint_image_map] at hm

/-- The support of a module `H` lies in the support of a module `K` of finite type, when the
vanishing of `K` on every chart over `U` forces the sections of `H` over `U` to vanish. -/
theorem supportOfSheaf_subset_of_forall_subsingleton (K H : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsFiniteTypeOnSite K]
    (hKH : ∀ U : SmallEtale B S hS X.1,
      (∀ (V : SmallEtale B S hS X.1) (_ : V ⟶ U), Subsingleton (K.val.obj (op V))) →
        Subsingleton (H.val.obj (op U))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj H) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj K) := by
  rintro x ⟨p, hp, hH⟩
  by_contra hK
  have hsub : Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj K).obj ⋙ forget AddCommGrpCat)) := by
    by_contra hc
    exact hK ⟨p, hp, hc⟩
  obtain ⟨U, hU⟩ := exists_zero_neighborhood_of_isFiniteTypeOnSite B S hS X.1 X.2 (𝟙 K) p hsub
  exact hH (subsingleton_stalkSet_of_forall_subsingleton B S hS X _ U fun V g =>
    hKH V fun W k => hU W (k ≫ g))

/-- **The support of `𝓗om(M, N)` lies in the support of `M`**, for `M` of finite type: where the
stalk of `M` vanishes, `M` vanishes on an étale neighbourhood, and so does `𝓗om(M, N)`. -/
theorem supportOfSheaf_smallEtaleInternalHomSmall_subset_left (M N : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsFiniteTypeOnSite M] :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (smallEtaleInternalHomSmall B S hS X.1 X.2 M N)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) :=
  supportOfSheaf_subset_of_forall_subsingleton B S hS X M _ fun U hU =>
    subsingleton_smallEtaleInternalHomSmall_obj B S hS X M N U (Or.inl hU)

/-- **The support of `𝓗om(M, N)` lies in the support of `N`**, for `N` of finite type. -/
theorem supportOfSheaf_smallEtaleInternalHomSmall_subset_right
    (M N : Modules.{u, u} B S hS X.1 X.2) [SheafOfModules.IsFiniteTypeOnSite N] :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (smallEtaleInternalHomSmall B S hS X.1 X.2 M N)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) :=
  supportOfSheaf_subset_of_forall_subsingleton B S hS X N _ fun U hU =>
    subsingleton_smallEtaleInternalHomSmall_obj B S hS X M N U (Or.inr hU)

/-- **The support of `𝓗om(M, N)` lies in the intersection of the supports of `M` and `N`**, for
`M` and `N` of finite type. -/
theorem supportOfSheaf_smallEtaleInternalHomSmall_subset_inter
    (M N : Modules.{u, u} B S hS X.1 X.2) [SheafOfModules.IsFiniteTypeOnSite M]
    [SheafOfModules.IsFiniteTypeOnSite N] :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (smallEtaleInternalHomSmall B S hS X.1 X.2 M N)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∩
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) :=
  fun _ hx => ⟨supportOfSheaf_smallEtaleInternalHomSmall_subset_left B S hS X M N hx,
    supportOfSheaf_smallEtaleInternalHomSmall_subset_right B S hS X M N hx⟩

/-- **`𝓗om(M, N)` has proper support** when the intersection of the supports of the coherent
modules `M` and `N` is proper over the target of a morphism locally of finite type. -/
theorem hasProperSupport_smallEtaleInternalHomSmall {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X.1 ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (M N : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 M]
    [IsCoherent B S hS X.1 X.2 N]
    (hcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∩
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N)))
    (hMN : IsProperOver B S hS X.2 hY f hf
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∩
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N)) hcl) :
    HasProperSupport B S hS X.2 hY f hf
      ((SheafOfModules.toSheaf _).obj (smallEtaleInternalHomSmall B S hS X.1 X.2 M N)) := by
  have : IsCoherent B S hS X.1 X.2 (smallEtaleInternalHomSmall B S hS X.1 X.2 M N) :=
    isCoherent_smallEtaleInternalHomSmall B S hS X.1 X.2 M N
  have hft : ∀ K : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 K →
      SheafOfModules.IsFiniteTypeOnSite K := fun K _ =>
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType K inferInstance
  have := hft M inferInstance
  have := hft N inferInstance
  have := hft (smallEtaleInternalHomSmall B S hS X.1 X.2 M N) inferInstance
  have hHcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2
    (smallEtaleInternalHomSmall B S hS X.1 X.2 M N)
  exact ⟨hHcl, isProperOver_of_subset B S hS X.2 hY f hf _ _ hHcl hcl
    (supportOfSheaf_smallEtaleInternalHomSmall_subset_inter B S hS X M N) hMN⟩

end AlgebraicGeometry.Space
