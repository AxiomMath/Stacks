module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.Thickenings.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of the conormal sheaf is detected by a flat base change

Let `h : Z ⟶ S` be a formally unramified morphism of schemes whose conormal sheaf `𝒞_{Z/S}` is
finite locally free. Suppose that every point of `Z` is in the image of the source leg of some
cartesian square
```
Z' --h'--→ S'
|          |
α          β
↓          ↓
Z ---h---→ S
```
with `β` flat and with `𝒞_{Z'/S'}` finite locally free *of rank `n`*. Then `𝒞_{Z/S}` is finite
locally free of rank `n`.

The two ingredients are flat base change for the conormal sheaf — the conormal sheaf of `h'` is
the pullback along `α` of the conormal sheaf of `h`, which is the conormal-sheaf conclusion of
[Stacks Project, Tag 04F9] — and the fact that the rank of a finite locally free sheaf is
detected at a single point of a nonempty scheme.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictPullbackIso`: the restriction to `g ⁻¹ᵁ V` of a
  pullback `g^* M` is the pullback of `M|_V` along `g ∣_ V`.
* `AlgebraicGeometry.universalConormalSheafFlatBaseChangeIso`: for a cartesian square with flat
  base `β`, the conormal sheaf of the base change is the pullback of the conormal sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_obj`: the pullback of a
  finite locally free sheaf of rank `r` along an arbitrary morphism of schemes is finite locally
  free of rank `r`.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_universalConormalSheaf_of_forall_isPullback`:
  finite local freeness of a given rank for the conormal sheaf of a formally unramified morphism
  may be checked after flat base change, on a family of squares covering the source.

## Implementation notes

The conormal sheaf of [Stacks Project, Tag 04F4] is `Stacks.Thickenings.universalConormalSheaf`,
built from the conormal sheaf of an *immersion*; the morphism of conormal sheaves induced by a
commutative square is therefore taken in the matching spelling
`Stacks.Thickenings.universalImmersionConormalSheafMap`, whose invertibility under a flat base
change is `Stacks.Thickenings.isIso_immersionConormalSheafMap_of_isPullback_of_flat`.

No flatness is used for the comparison of ranks: once the conormal sheaf of `h'` is identified
with a pullback of the conormal sheaf of `h`, the rank of the pullback is the rank of the
original for *any* morphism, and the two candidate ranks are compared at the chosen point `z'`
of the nonempty open `α ⁻¹ᵁ V`.

## References

* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F9](https://stacks.math.columbia.edu/tag/04F9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings (universalConormalSheaf universalFirstOrderThickening
  universalImmersionConormalSheafMap)

universe u

namespace AlgebraicGeometry

/-- **Restriction of a pullback is a pullback of a restriction.** For a morphism of schemes
`g : X ⟶ Y`, an open `V` of `Y` and a sheaf of modules `M` on `Y`, the restriction to the
preimage `g ⁻¹ᵁ V` of the pullback `g^* M` is the pullback of `M|_V` along the restricted
morphism `g ∣_ V`.

Both sides are pullbacks of `M` along the two equal composites of
`AlgebraicGeometry.morphismRestrict_ι`, read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
def Scheme.Modules.restrictPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    (M : Y.Modules) :
    ((Scheme.Modules.pullback g).obj M).restrict (g ⁻¹ᵁ V).ι ≅
      (Scheme.Modules.pullback (g ∣_ V)).obj (M.restrict V.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ V).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (g ⁻¹ᵁ V).ι g).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι g V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (g ∣_ V) V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ V)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm

/-- **The pullback of a finite locally free sheaf of rank `r` is finite locally free of rank
`r`.** No hypothesis on the morphism is needed: a pullback functor is additive and sends the
structure sheaf to the structure sheaf, so it sends a free sheaf of rank `r` to a free sheaf of
rank `r`.

This is `Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData` for the structure-sheaf
morphism of a morphism of schemes. -/
theorem Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_obj {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (r : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ((Scheme.Modules.pullback g).obj M) r :=
  have : (_root_.SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData g.base g.toRingCatSheafHom M r h

/-- **[Stacks Project, Tag 04F9] as an isomorphism of conormal sheaves.** For a cartesian square
```
Z' --h'--→ S'
|          |
α          β
↓          ↓
Z ---h---→ S
```
with `β` flat and `h` formally unramified, the conormal sheaf `𝒞_{Z'/S'}` of the base change is
the pullback along `α` of the conormal sheaf `𝒞_{Z/S}`.

The underlying morphism is `Stacks.Thickenings.universalImmersionConormalSheafMap`, the map of
[Stacks Project, Tag 04F7] in the spelling of [Stacks Project, Tag 01R2] in which
`Stacks.Thickenings.universalConormalSheaf` is built; it is invertible by
`Stacks.Thickenings.isIso_immersionConormalSheafMap_of_isPullback_of_flat`. -/
@[sga "3 I 6.8.5" "more general"]
def universalConormalSheafFlatBaseChangeIso {Z S Z' S' : Scheme.{u}} {h : Z ⟶ S} {h' : Z' ⟶ S'}
    {α : Z' ⟶ Z} {β : S' ⟶ S} [FormallyUnramified h] [FormallyUnramified h'] [Flat β]
    (sq : IsPullback h' α β h) :
    (Scheme.Modules.pullback α).obj (universalConormalSheaf h) ≅ universalConormalSheaf h' :=
  haveI hm : IsIso (C := Z'.Modules) (universalImmersionConormalSheafMap
      (universalFirstOrderThickening h') (universalFirstOrderThickening h) α β sq.w) :=
    Stacks.Thickenings.isIso_immersionConormalSheafMap_of_isPullback_of_flat
      (universalFirstOrderThickening h') sq (universalFirstOrderThickening h)
  @asIso Z'.Modules _ _ _ _ hm

/-- **Finite local freeness of a given rank for the conormal sheaf of a formally unramified
morphism may be checked after flat base change**, on a family of squares covering the source.

Let `h : Z ⟶ S` be formally unramified with finite locally free conormal sheaf, and suppose that
every point `z` of `Z` lies in the image of the source leg `α : Z' ⟶ Z` of a cartesian square
over `h` whose base map `β` is flat and whose conormal sheaf `𝒞_{Z'/S'}` is finite locally free
of rank `n`. Then `𝒞_{Z/S}` is finite locally free of rank `n`.

Finite local freeness gives an open `V ∋ z` over which `𝒞_{Z/S}` has *some* rank `s`. By
[Stacks Project, Tag 04F9], `𝒞_{Z'/S'}` is the pullback `α^* 𝒞_{Z/S}`, so its restriction to the
open `α ⁻¹ᵁ V` is both finite locally free of rank `s` — being the pullback of `𝒞_{Z/S}|_V`
along `α ∣_ V` — and finite locally free of rank `n`. That open contains the chosen point `z'`
over `z`, so `s = n`, and the Zariski-cover criterion
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top` finishes. -/
theorem isFiniteLocallyFreeOfRank_universalConormalSheaf_of_forall_isPullback
    {Z S : Scheme.{u}} (h : Z ⟶ S) [FormallyUnramified h] (n : ℕ)
    (hfl : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (universalConormalSheaf h))
    (H : ∀ z : Z, ∃ (Z' S' : Scheme.{u}) (h' : Z' ⟶ S') (α : Z' ⟶ Z) (β : S' ⟶ S)
            (sq : IsPullback h' α β h) (z' : Z'), Flat β ∧ α.base z' = z ∧
              (letI : FormallyUnramified h' :=
                 Stacks.Thickenings.formallyUnramified_of_isPullback sq
               SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (universalConormalSheaf h') n)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (universalConormalSheaf h) n := by
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff (universalConormalSheaf h) n).mp ?_
  have key : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧ Scheme.Modules.IsFiniteLocallyFreeOfRank
      ((Scheme.Modules.restrictFunctor V.ι).obj (universalConormalSheaf h)) n := by
    intro z
    obtain ⟨V, hzV, s, hs⟩ :=
      Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict
        (universalConormalSheaf h) hfl z
    obtain ⟨Z', S', h', α, β, sq, z', hβ, hz', hn⟩ := H z
    have := hβ
    let : FormallyUnramified h' := Stacks.Thickenings.formallyUnramified_of_isPullback sq
    have hmem : z' ∈ α ⁻¹ᵁ V := by
      change α.base z' ∈ V
      rwa [hz']
    have hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((Scheme.Modules.pullback α).obj (universalConormalSheaf h)).restrict (α ⁻¹ᵁ V).ι) s :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        (Scheme.Modules.restrictPullbackIso α V (universalConormalSheaf h)).symm
        (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_obj (α ∣_ V) _ s hs)
    have hB : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((Scheme.Modules.pullback α).obj (universalConormalSheaf h)).restrict (α ⁻¹ᵁ V).ι) n := by
      refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ n).mp
        (Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict (α ⁻¹ᵁ V).ι ?_)
      exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ n).mpr
        (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
          (universalConormalSheafFlatBaseChangeIso sq).symm hn)
    have hsn : s = n := Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ hA hB ⟨z', hmem⟩
    exact ⟨V, hzV, (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ n).mpr (hsn ▸ hs)⟩
  choose V hzV hV using key
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top V
    (le_antisymm le_top fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩) hV

end AlgebraicGeometry

end
