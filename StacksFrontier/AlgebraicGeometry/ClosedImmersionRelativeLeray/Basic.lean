module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasquePushforwardVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along a composite whose first factor is a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `f : X ⟶ S` an arbitrary morphism. For
every sheaf of modules `G` on `Z` and every degree `n`,

`Rⁿ (i ≫ f)_* G ≅ Rⁿ f_* (i_* G)`,

naturally in `G`. This is the degenerate case of the relative Leray spectral sequence
([Stacks, Tag 01F6]) in which the inner morphism contributes only in degree `0`, as used in the
proof of [Stacks, Tag 02O5]: *"as `Z → X` is a closed immersion … hence by the relative Leray
spectral sequence we will have `R^p f_* F = R^p g_* G` for `p > 0` and `f_* F = g_* G`"*.

The pushforward `i_*` of an injective sheaf of modules is flasque for any morphism `i`
([Stacks, Tag 01EX] part (2)), hence right acyclic for `f_*` ([Stacks, Tag 09T0]), and `i_*` is
exact when `i` is a closed immersion.

## Main results

* `Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isFlasque_toSheaf_modulePushforward`:
  the abelian sheaf underlying the pushforward of an injective sheaf of modules along a morphism
  of ringed spaces is flasque.
* `…ClosedImmersionRelativeLeray.rightAcyclic_pushforward_pushforward_obj_of_injective`:
  `i_* I` is right acyclic for `f_*` when `I` is injective, for arbitrary `i` and `f`.
* `…ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso`: the isomorphism of functors
  `Rⁿ (i ≫ f)_* ≅ i_* ⋙ Rⁿ f_*` for `i` a closed immersion.
* `…ClosedImmersionRelativeLeray.forall_isCoherent_rightDerived_pushforward_iff`: for `i` a
  closed immersion, every `Rⁿ (i ≫ f)_* G` is coherent if and only if every `Rⁿ f_* (i_* G)` is.
* `…ClosedImmersionRelativeLeray.forall_isCoherent_rightDerived_pushforward_pushforward`: if
  `Rⁿ (i ≫ f)_* G` vanishes for `n > 0` and `(i ≫ f)_* G` is coherent, then every
  `Rⁿ f_* (i_* G)` is coherent.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The pushforward of an injective module is flasque, hence acyclic -/

/-- **The pushforward of an injective sheaf of modules is flasque.** For any morphism of ringed
spaces `f : X ⟶ Y` and any injective `I`, the abelian sheaf underlying `f_* I` has surjective
restriction maps. -/
theorem isFlasque_toSheaf_modulePushforward
    {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (I : SheafOfModules.{u} (structureSheafRing X)) (hI : Injective I) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (structureSheafRing Y)).obj
        ((RingedSpaceModuleAdjunction.modulePushforward f).obj I)) := by
  constructor
  intro U V m
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro s
  have hY : V.unop ≤ U.unop := leOfHom m.unop
  have hX : ((RingedSpaceModuleAdjunction.opensMap f).obj V.unop) ≤
      ((RingedSpaceModuleAdjunction.opensMap f).obj U.unop) := fun x hx => hY hx
  obtain ⟨t, ht⟩ := (@Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
    _ _ (structureSheafRing X) I hI _ _ hX) s
  refine ⟨t, ?_⟩
  change (I.val.presheaf.map
    (((RingedSpaceModuleAdjunction.opensMap f).map (homOfLE hY)).op)) t = s
  simpa [RingedSpaceModuleAdjunction.modulePushforward,
    RingedSpaceModuleAdjunction.structureSheafHom] using ht

/-- **The pushforward of an injective module is right acyclic for a further pushforward.** For
morphisms of schemes `i : Z ⟶ X` and `f : X ⟶ S` and an injective `I` on `Z`, the module `i_* I`
is right acyclic for `f_*`: all its positive higher direct images along `f` vanish. -/
@[ega "0 12.2.4" "special case"]
theorem rightAcyclic_pushforward_pushforward_obj_of_injective {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) (I : Z.Modules) (hI : Injective I) :
    (AlgebraicGeometry.Scheme.Modules.pushforward f).rightAcyclic
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj I) := by
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n _).2 ?_
  exact
    @Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
      _ _ (Stacks.Cohomology.AffineBase.asRingedSpaceHom f) _
      (isFlasque_toSheaf_modulePushforward
        (Stacks.Cohomology.AffineBase.asRingedSpaceHom i) I hI)
      (n : ℤ) (by exact_mod_cast hn)

/-! ### The higher direct images of a composite through a closed immersion -/

/-- **`Rⁿ (i ≫ f)_* ≅ i_* ⋙ Rⁿ f_*` for a closed immersion `i`.** The degenerate relative
Leray comparison, as an isomorphism of functors `Z.Modules ⥤ S.Modules`, for every `n`. -/
noncomputable def rightDerivedPushforwardCompIso {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.IsClosedImmersion i] (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n ≅
      AlgebraicGeometry.Scheme.Modules.pushforward i ⋙
        (AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n :=
  (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp i f) n).symm ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
      (AlgebraicGeometry.Scheme.Modules.pushforward i)
      (AlgebraicGeometry.Scheme.Modules.pushforward f)
      (fun I hI => rightAcyclic_pushforward_pushforward_obj_of_injective i f I hI) n

/-- **`Rⁿ (i ≫ f)_* G ≅ Rⁿ f_* (i_* G)`**, the comparison at a fixed module. -/
noncomputable def rightDerivedPushforwardObjIso {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) (n : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj G ≅
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) :=
  (rightDerivedPushforwardCompIso i f n).app G

/-- Coherence of a module on a scheme is invariant under isomorphism. -/
private theorem isCoherent_iff_of_iso {S : AlgebraicGeometry.Scheme.{u}} {M N : S.Modules}
    (e : M ≅ N) : M.IsCoherent ↔ N.IsCoherent :=
  ⟨fun h => have := h
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf) e.symm,
   fun h => have := h
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf) e⟩

/-- **Coherence transports across the comparison.** `Rⁿ f_* (i_* G)` is coherent if and only if
`Rⁿ (i ≫ f)_* G` is. -/
theorem isCoherent_rightDerived_pushforward_iff {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) (n : ℕ) :
    (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).IsCoherent ↔
      (((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj
        G).IsCoherent :=
  isCoherent_iff_of_iso (rightDerivedPushforwardObjIso i f G n).symm

/-- **Vanishing transports across the comparison.** `Rⁿ f_* (i_* G)` vanishes if and only if
`Rⁿ (i ≫ f)_* G` does. -/
theorem isZero_rightDerived_pushforward_iff {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) (n : ℕ) :
    IsZero (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)) ↔
      IsZero (((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj G) :=
  ⟨fun h => h.of_iso (rightDerivedPushforwardObjIso i f G n),
   fun h => h.of_iso (rightDerivedPushforwardObjIso i f G n).symm⟩

/-! ### Coherence of the higher direct images -/

/-- Write `P` for the property of a module that all of its higher direct images along a given
morphism are coherent. For `i : Z ⟶ X` a closed immersion and `f : X ⟶ S` arbitrary, `P` holds for
`G` along `i ≫ f` if and only if it holds for `i_* G` along `f`. -/
theorem forall_isCoherent_rightDerived_pushforward_iff {Z X S : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (f : X ⟶ S) [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) :
    (∀ n : ℕ, (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).IsCoherent) ↔
      (∀ n : ℕ, (((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj
        G).IsCoherent) :=
  ⟨fun h n => (isCoherent_rightDerived_pushforward_iff i f G n).1 (h n),
   fun h n => (isCoherent_rightDerived_pushforward_iff i f G n).2 (h n)⟩

/-- Let `i : Z ⟶ X` be a closed immersion. If the higher direct images of `G` along `i ≫ f`
vanish in positive degrees and the direct image `(i ≫ f)_* G` is coherent, then every higher
direct image of `i_* G` along `f` is coherent. -/
theorem forall_isCoherent_rightDerived_pushforward_pushforward
    {Z X S : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules)
    (hvanish : ∀ n : ℕ, 0 < n →
      IsZero (((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj G))
    (hzero : ((AlgebraicGeometry.Scheme.Modules.pushforward (i ≫ f)).obj G).IsCoherent)
    (n : ℕ) :
    (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived n).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).IsCoherent := by
  refine (isCoherent_rightDerived_pushforward_iff i f G n).2 ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (isCoherent_iff_of_iso
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroObjIso
        (i ≫ f) G)).2 hzero
  · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (R := S.ringCatSheaf)
      (hvanish n hn)

end Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray

end
