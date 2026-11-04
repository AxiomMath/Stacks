module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyCompatible
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapDeltaFunctor
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The derived base change map on cohomology sheaves

Let `h ≫ f' = e ≫ g` be a commutative square of schemes,

```
Y  --h-->  X'
|e         |f'
v          v
T  --g-->  S
```

and let `L` be an object of `D^+(T_étale)`, `M` one of `D^+(Y_étale)` and `κ : Re^{-1}L ⟶ M` a
map. Reading the derived base change comparison `R(f')^{-1}Rg_* ⟶ Rh_*Re^{-1}` of
[Stacks, Tag 0F02] on degree-`p` cohomology sheaves, and following it by `H^p(Rh_*κ)`, gives a
map

`(f')^{-1}H^p(Rg_*L) ⟶ H^p(Rh_*M)`,

the source being identified with `H^p(R(f')^{-1}Rg_*L)` by exactness of `(f')^{-1}`. For `L` and
`M` sheaves placed in degree zero this is the base change map on higher direct images followed
by `R^ph_*κ`. This is the map all colimit assertions for higher direct images of complexes along
a limit of schemes are about ([Stacks, Tag 0GIU], [Stacks, Tag 0GIV]), and this file proves the
three properties those assertions use.

## Main definitions

* `Stacks.EtaleCohomology.derivedBaseChangeHomologyMap`: the map above.

## Main results

* `Stacks.EtaleCohomology.derivedBaseChangeHomologyMap_naturality`: the map is natural in the
  triple `(L, M, κ)`.
* `Stacks.EtaleCohomology.derivedBaseChangeHomologyMap_homologySequenceδ`: the map commutes with
  the connecting morphisms of the long exact cohomology sequences of a triangle `L₁ → L₂ → L₃` on
  `T`, a triangle `M₁ → M₂ → M₃` on `Y` and a morphism of triangles from `Re^{-1}` of the first
  to the second.
* `Stacks.EtaleCohomology.derivedBaseChangeHomologyMap_paste`: **the pasting law**: for two
  horizontally composable squares the map of the outer rectangle is the inverse image of the map
  of the first square followed by the map of the second, read through the comparison of inverse
  images along the composite. The composites are named, as in
  `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app_named`.

## Implementation notes

The connecting morphism compatibility is the composite of three: that of the exact functor
`(f')^{-1}` with cohomology
(`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_homologySequenceδ`), that of the derived
base change comparison, which is compatible with the shift
(`Stacks.EtaleCohomology.commShift_smallEtaleDerivedBaseChangeAb`), and the naturality of the
connecting morphism along `Rh_*` of the morphism of triangles. The pasting law is the derived
pasting law `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app` together
with the cocycle identity `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_comp` of the
identification of the source.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

section Map

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) (p : ℤ)

/-- **The derived base change map on cohomology sheaves**, `(f')^{-1}H^p(Rg_*L) ⟶ H^p(Rh_*M)`,
attached to a map `κ : Re^{-1}L ⟶ M`: the derived base change comparison at `L` read on
degree-`p` cohomology sheaves, followed by `H^p(Rh_*κ)`, the source being identified with
`H^p(R(f')^{-1}Rg_*L)` by exactness of `(f')^{-1}`. -/
def derivedBaseChangeHomologyMap
    (L : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1}))
    (κ : (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj L ⟶ M) :
    (smallEtalePullbackAb f').obj ((DerivedCategory.Plus.homologyFunctor _ p).obj
        ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj L)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ p).obj
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.obj M) :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f') p).inv.app
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj L) ≫
    (DerivedCategory.Plus.homologyFunctor _ p).map
      ((smallEtaleDerivedBaseChangeAb f' g h e w).app L) ≫
    (DerivedCategory.Plus.homologyFunctor _ p).map
      ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map κ)

/-- **The derived base change map on cohomology sheaves is natural in its data.** Maps
`α : L ⟶ L₁` and `β : M ⟶ M₁` compatible with `κ` and `κ₁` commute with the two maps. -/
theorem derivedBaseChangeHomologyMap_naturality
    {L L₁ : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1})}
    {M M₁ : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})}
    (κ : (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj L ⟶ M)
    (κ₁ : (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj L₁ ⟶ M₁) (α : L ⟶ L₁) (β : M ⟶ M₁)
    (hκ : (smallEtalePullbackAb e).rightDerivedFunctorPlus.map α ≫ κ₁ = κ ≫ β) :
    (smallEtalePullbackAb f').map ((DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.map α)) ≫
        derivedBaseChangeHomologyMap f' g h e w p L₁ M₁ κ₁ =
      derivedBaseChangeHomologyMap f' g h e w p L M κ ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map β) := by
  have h1 := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
    (smallEtalePullbackAb f') p).inv.naturality
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.map α)
  have h2 := (smallEtaleDerivedBaseChangeAb f' g h e w).naturality α
  dsimp only [Functor.comp_map] at h1 h2
  dsimp only [derivedBaseChangeHomologyMap]
  rw [← Category.assoc, h1]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun z => (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (smallEtalePullbackAb f') p).inv.app
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj L) ≫
      (DerivedCategory.Plus.homologyFunctor _ p).map z)
    (by rw [← Category.assoc, h2, Category.assoc, ← Functor.map_comp, hκ])

end Map

/-! ### Compatibility with the connecting morphisms -/

section Delta

private theorem delta_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : 𝒳}
    {e₃ : o₀ ⟶ o₁} {t₃ : o₁ ⟶ o₂} {k₃ : o₂ ⟶ o₃} {δ' : o₃ ⟶ o₄}
    {δM : o₂ ⟶ o₅} {k₁ : o₅ ⟶ o₄} {δF : o₁ ⟶ o₆} {t₁ : o₆ ⟶ o₅} {e₁ : o₇ ⟶ o₆}
    {δG : o₀ ⟶ o₇}
    (hk : k₃ ≫ δ' = δM ≫ k₁) (ht : t₃ ≫ δM = δF ≫ t₁) (he : e₃ ≫ δF = δG ≫ e₁) :
    (e₃ ≫ t₃ ≫ k₃) ≫ δ' = δG ≫ (e₁ ≫ t₁ ≫ k₁) := by
  rw [Category.assoc, Category.assoc, hk, reassoc_of% ht, reassoc_of% he]

private theorem inv_delta_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ : 𝒳}
    {i₃ : o₀ ⟶ o₁} {δ : o₁ ⟶ o₂} {j₁ : o₂ ⟶ o₃} {i₁ : o₃ ⟶ o₂} {x : o₀ ⟶ o₃}
    (h : i₃ ≫ δ ≫ j₁ = x) (hij : j₁ ≫ i₁ = 𝟙 _) : i₃ ≫ δ = x ≫ i₁ := by
  rw [← h, Category.assoc, Category.assoc, hij, Category.comp_id]

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

attribute [local instance] commShift_smallEtaleDerivedBaseChangeAb

/-- **The derived base change map on cohomology sheaves commutes with the connecting
morphisms.** For a triangle `T₀` on `T`, a triangle `T₁` on `Y` and a morphism of triangles
`φ : Re^{-1}T₀ ⟶ T₁`, the maps in degrees `n₀` and `n₀ + 1` attached to the first and third
components of `φ` form a commuting square with the connecting morphism of `Rg_*T₀`, pulled back
along `f'`, and that of `Rh_*T₁`. -/
theorem derivedBaseChangeHomologyMap_homologySequenceδ
    (T₀ : Triangle (DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1})))
    (T₁ : Triangle (DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})))
    (φ : (smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj T₀ ⟶ T₁)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    derivedBaseChangeHomologyMap f' g h e w n₀ T₀.obj₃ T₁.obj₃ φ.hom₃ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
          ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj T₁) n₀ n₁ hn =
      (smallEtalePullbackAb f').map
          ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
            ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj T₀) n₀ n₁ hn) ≫
        derivedBaseChangeHomologyMap f' g h e w n₁ T₀.obj₁ T₁.obj₁ φ.hom₁ := by
  have hk : (DerivedCategory.Plus.homologyFunctor _ n₀).map
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map φ.hom₃) ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj T₁) n₀ n₁ hn =
      (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj
          ((smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj T₀)) n₀ n₁ hn ≫
      (DerivedCategory.Plus.homologyFunctor _ n₁).map
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map φ.hom₁) :=
    (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_naturality
      ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.map φ) n₀ n₁ hn
  have ht' := Stacks.Triangulated.homologySequenceδ_natTrans
    (DerivedCategory.Plus.homologyFunctor _ 0) (smallEtaleDerivedBaseChangeAb f' g h e w) T₀
    n₀ n₁ hn
  rw [homologySequenceδ_mapTriangle_comp, homologySequenceδ_mapTriangle_comp] at ht'
  have ht : (DerivedCategory.Plus.homologyFunctor _ n₀).map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app T₀.obj₃) ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj
          ((smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj T₀)) n₀ n₁ hn =
      (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
        ((smallEtalePullbackAb f').rightDerivedFunctorPlus.mapTriangle.obj
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj T₀)) n₀ n₁ hn ≫
      (DerivedCategory.Plus.homologyFunctor _ n₁).map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app T₀.obj₁) := ht'
  have he := inv_delta_chain
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_homologySequenceδ
      (smallEtalePullbackAb f')
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj T₀) n₀ n₁ hn)
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f')
      n₁).hom_inv_id_app _)
  exact delta_chain hk ht he

end Delta

/-! ### The pasting law -/

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)

/-- The comparison `R(v₁^{-1}) ⋙ R(v₂^{-1}) ≅ R(v^{-1})` of derived inverse images along a named
composite `v = v₂ ≫ v₁`. -/
def smallEtaleDerivedPullbackAbPlusComp' (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁) :
    (smallEtalePullbackAb v₁).rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb v₂).rightDerivedFunctorPlus ≅
      (smallEtalePullbackAb v).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact (smallEtalePullbackAb v₁)
    (smallEtalePullbackAb v₂) (smallEtalePullbackAb v) (smallEtalePullbackAbComp' v₂ v₁ v hv)

/-- **The pasting law for the underived base change map with the composite legs named**:
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste_app` for legs `u` and `v` given together
with equations identifying them with the composites. -/
theorem smallEtaleBaseChangeAb_paste_app_named (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀)
    (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀)
    (hv : v = v₂ ≫ v₁) (w : g₂ ≫ u = v ≫ g₀) (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (smallEtaleBaseChangeAb u g₀ g₂ v w).app F =
      (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app ((smallEtalePushforwardAb g₀).obj F) ≫
        (smallEtalePullbackAb u₂).map ((smallEtaleBaseChangeAb u₁ g₀ g₁ v₁ w₁).app F) ≫
          (smallEtaleBaseChangeAb u₂ g₁ g₂ v₂ w₂).app ((smallEtalePullbackAb v₁).obj F) ≫
            (smallEtalePushforwardAb g₂).map
              ((smallEtalePullbackAbComp' v₂ v₁ v hv).hom.app F) := by
  subst hu hv
  -- the kernel compares the proof arguments only after unfolding the base change maps, so the
  -- commutativity proof is first replaced by the one the unnamed pasting law is stated with
  obtain rfl : w = smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ := rfl
  simpa [smallEtalePullbackAbComp'] using
    smallEtaleBaseChangeAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ F

/-- **The derived pasting law with the two composite legs named**:
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app` for legs `u` and `v`
given together with equations identifying them with the composites. -/
theorem smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app_named (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀)
    (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀)
    (hv : v = v₂ ≫ v₁) (w : g₂ ≫ u = v ≫ g₀)
    (L₀ : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})) :
    (smallEtaleDerivedBaseChangeAb u g₀ g₂ v w).app L₀ =
      (smallEtaleDerivedPullbackAbPlusComp' u₁ u₂ u hu).inv.app
          ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀) ≫
        (smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀) ≫
          (smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
              ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj L₀) ≫
            (smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
              ((smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).hom.app L₀) :=
  Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app
    (smallEtalePushforwardAb g₀) (smallEtalePushforwardAb g₁) (smallEtalePushforwardAb g₂)
    (smallEtalePullbackAb u₁) (smallEtalePullbackAb u₂) (smallEtalePullbackAb u)
    (smallEtalePullbackAb v₁) (smallEtalePullbackAb v₂) (smallEtalePullbackAb v)
    (smallEtalePullbackAbComp' u₂ u₁ u hu) (smallEtalePullbackAbComp' v₂ v₁ v hv) _ _ _
    (smallEtaleBaseChangeAb_paste_app_named g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ u hu v hv w) L₀

/-- **The cocycle identity for the cohomology comparison of the inverse image, with the
composite named**: `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_comp` for the inverse
images along `u₁`, `u₂` and a morphism `u` given with an equation `u = u₂ ≫ u₁`. -/
theorem exactRightDerivedPlusHomologyIso_smallEtalePullbackAb_comp_named (u : S₂ ⟶ S₀)
    (hu : u = u₂ ≫ u₁) (p : ℤ)
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology S₀) Ab.{u + 1})) :
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u) p).inv.app M ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedPullbackAbPlusComp' u₁ u₂ u hu).inv.app M) =
      (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app _ ≫
        (smallEtalePullbackAb u₂).map
          ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₁)
            p).inv.app M) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₂)
          p).inv.app ((smallEtalePullbackAb u₁).rightDerivedFunctorPlus.obj M) :=
  congr_app (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_comp
    (smallEtalePullbackAb u₁) (smallEtalePullbackAb u₂) (smallEtalePullbackAb u)
    (smallEtalePullbackAbComp' u₂ u₁ u hu) p) M

private theorem paste_chain {𝒳 : Type*} [Category* 𝒳]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ o₁₁ : 𝒳}
    {eU : o₀ ⟶ o₁} {Hτ : o₁ ⟶ o₄} {Hκ : o₄ ⟶ o₇} {HcU : o₁ ⟶ o₂} {HA : o₂ ⟶ o₃}
    {Ht₂ : o₃ ⟶ o₅} {HcV' : o₅ ⟶ o₄} {HcV : o₄ ⟶ o₅} {Hm : o₅ ⟶ o₆} {Hκ₂ : o₆ ⟶ o₇}
    {c : o₀ ⟶ o₈} {X : o₈ ⟶ o₁₀} {U₁ : o₈ ⟶ o₉} {e₂ : o₉ ⟶ o₂} {U₂ : o₉ ⟶ o₁₀}
    {e₂' : o₁₀ ⟶ o₁₁} {HB : o₂ ⟶ o₁₁} {Ht₂' : o₁₁ ⟶ o₆} {HA' : o₃ ⟶ o₁₁}
    (hτ : Hτ = HcU ≫ HA ≫ Ht₂ ≫ HcV') (hκ : Hκ = HcV ≫ Hm ≫ Hκ₂) (hX : X = U₁ ≫ U₂)
    (hc : eU ≫ HcU = c ≫ U₁ ≫ e₂) (hV : HcV' ≫ HcV = 𝟙 _)
    (hn : HA' ≫ Ht₂' = Ht₂ ≫ Hm) (hB : HB = HA ≫ HA') (he : U₂ ≫ e₂' = e₂ ≫ HB) :
    eU ≫ Hτ ≫ Hκ = c ≫ X ≫ e₂' ≫ Ht₂' ≫ Hκ₂ := by
  rw [hτ, hκ, hX]
  simp only [Category.assoc]
  rw [reassoc_of% hV, ← reassoc_of% hn, ← reassoc_of% hB, reassoc_of% he, ← reassoc_of% hc]

variable (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (p : ℤ)
  (L₀ : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}))
  (L₁ : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}))
  (L₂ : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₂) Ab.{u + 1}))
  (κ₁ : (smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj L₀ ⟶ L₁)
  (κ₂ : (smallEtalePullbackAb v₂).rightDerivedFunctorPlus.obj L₁ ⟶ L₂)

private theorem paste_hτ (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁)
    (w : g₂ ≫ u = v ≫ g₀) :
    (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtaleDerivedBaseChangeAb u g₀ g₂ v w).app L₀) =
      (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedPullbackAbPlusComp' u₁ u₂ u hu).inv.app
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀)) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
            ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj L₀)) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).hom.app L₀)) := by
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app_named g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ u hu v
    hv w L₀]
  simp only [Functor.map_comp]

private theorem paste_hX :
    (smallEtalePullbackAb u₂).map (derivedBaseChangeHomologyMap u₁ g₀ g₁ v₁ w₁ p L₀ L₁ κ₁) =
      (smallEtalePullbackAb u₂).map
          ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₁)
            p).inv.app ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) ≫
        (smallEtalePullbackAb u₂).map ((DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀ ≫
            (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map κ₁)) := by
  rw [← Functor.map_comp, Functor.map_comp (DerivedCategory.Plus.homologyFunctor _ p)]
  rfl

private theorem paste_hc (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) :
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u)
          p).inv.app ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedPullbackAbPlusComp' u₁ u₂ u hu).inv.app
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) =
      (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app _ ≫
        (smallEtalePullbackAb u₂).map
          ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₁)
            p).inv.app ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₂)
          p).inv.app ((smallEtalePullbackAb u₁).rightDerivedFunctorPlus.obj
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) :=
  exactRightDerivedPlusHomologyIso_smallEtalePullbackAb_comp_named u₁ u₂ u hu p _

private theorem paste_hV (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁) :
    (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
          ((smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).hom.app L₀)) ≫
      (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
          ((smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).inv.app L₀)) = 𝟙 _ := by
  rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

private theorem paste_hn :
    (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
          ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map κ₁)) ≫
      (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app L₁) =
    (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
          ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj L₀)) ≫
      (DerivedCategory.Plus.homologyFunctor _ p).map
        ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
          ((smallEtalePullbackAb v₂).rightDerivedFunctorPlus.map κ₁)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).naturality κ₁)

private theorem paste_he :
    (smallEtalePullbackAb u₂).map ((DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀ ≫
            (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map κ₁)) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₂)
          p).inv.app ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.obj L₁) =
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₂)
          p).inv.app ((smallEtalePullbackAb u₁).rightDerivedFunctorPlus.obj
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj L₀)) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀ ≫
              (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map κ₁)) :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
    (smallEtalePullbackAb u₂) p).inv.naturality
    ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app L₀ ≫
      (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map κ₁)

/-- **The pasting law for the derived base change map on cohomology sheaves.** For two
horizontally composable commutative squares with composite legs `u = u₂ ≫ u₁` and
`v = v₂ ≫ v₁`, the map of the outer rectangle attached to the composite
`Rv^{-1}L₀ ≅ Rv₂^{-1}Rv₁^{-1}L₀ ⟶ Rv₂^{-1}L₁ ⟶ L₂` is the inverse image along `u₂` of the map of
the first square followed by the map of the second, read through the comparison of inverse
images along `u`. -/
theorem derivedBaseChangeHomologyMap_paste (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀)
    (hv : v = v₂ ≫ v₁) (w : g₂ ≫ u = v ≫ g₀) :
    derivedBaseChangeHomologyMap u g₀ g₂ v w p L₀ L₂
        ((smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).inv.app L₀ ≫
          (smallEtalePullbackAb v₂).rightDerivedFunctorPlus.map κ₁ ≫ κ₂) =
      (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app _ ≫
        (smallEtalePullbackAb u₂).map (derivedBaseChangeHomologyMap u₁ g₀ g₁ v₁ w₁ p L₀ L₁ κ₁) ≫
          derivedBaseChangeHomologyMap u₂ g₁ g₂ v₂ w₂ p L₁ L₂ κ₂ :=
  paste_chain (paste_hτ g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ p L₀ u hu v hv w)
    (by simp only [Functor.map_comp]) (paste_hX g₀ g₁ u₁ u₂ v₁ w₁ p L₀ L₁ κ₁)
    (paste_hc g₀ u₁ u₂ p L₀ u hu) (paste_hV g₂ v₁ v₂ p L₀ v hv)
    (paste_hn g₁ g₂ u₂ v₁ v₂ w₂ p L₀ L₁ κ₁) (by simp only [Functor.map_comp])
    (paste_he g₀ g₁ u₁ u₂ v₁ w₁ p L₀ L₁ κ₁)

end Paste

end Stacks.EtaleCohomology

end
