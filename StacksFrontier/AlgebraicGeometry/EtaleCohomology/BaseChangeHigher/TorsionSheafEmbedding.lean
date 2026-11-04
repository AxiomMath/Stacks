module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LadderAssembly
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The resolution of [Stacks, Tag 0F03] by injective sheaves of `ℤ/nℤ`-modules

The proof of [Stacks, Tag 0F03] begins: *choose a short exact sequence
`0 → F → I → Q → 0` where `I` is an injective sheaf of `ℤ/nℤ`-modules*. This file makes that
choice, and with it the comparison ladder of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/LadderAssembly.lean` becomes a
construction rather than a hypothesis, so the three assertions of the tag are proved from the
tag's own hypotheses.

What the choice needs is the identification of the abelian sheaves on the small étale site of
`T` annihilated by `n` with the sheaves of modules over the constant sheaf of rings `ℤ/nℤ`:
that is `Stacks.Cohomology.ZModSheaf.torsionSheafToModules` together with
`Stacks.Cohomology.ZModSheaf.torsionSheafToModulesIso`, and this file instantiates them at the
small étale site, where sheaves of modules over a sheaf of rings have enough injectives
(`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`). Injectivity as a sheaf of
`ℤ/nℤ`-modules is exactly what makes the middle term of the sequence acyclic for the direct
image — `Stacks.EtaleCohomology.isZero_higherBaseChangeSource_toSheaf_succ`, which is
[Stacks, Tag 03FD] — while keeping it, and hence its quotient, annihilated by `n`; an injective
*abelian* sheaf containing `F` would be neither.

## Main definitions

* `Stacks.EtaleCohomology.etaleZModRingSheaf` — the constant sheaf of rings `ℤ/nℤ` on the small
  étale site of `T`.
* `Stacks.EtaleCohomology.torsionEtaleModule` — an abelian sheaf on the small étale site of `T`
  annihilated by `n`, read as a sheaf of `ℤ/nℤ`-modules, with
  `Stacks.EtaleCohomology.torsionEtaleModuleIso` identifying its underlying abelian sheaf with
  the original sheaf.
* `Stacks.EtaleCohomology.torsionEtaleInjectiveEmbedding` — **the embedding of [Stacks, Tag
  0F03]**: an abelian sheaf annihilated by `n` inside the underlying abelian sheaf of an
  injective sheaf of `ℤ/nℤ`-modules.

## Main results

* `Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π` — a monomorphism and its cokernel
  form a short exact sequence.
* `Stacks.EtaleCohomology.zsmul_toSheaf_etaleZModRingSheaf_eq_zero` — the sections of the
  underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules are annihilated by `n`.
* `Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_annihilated` — **part (1) of
  [Stacks, Tag 0F03]**: the base change map `(f')⁻¹R^{q+1}g_* F → R^{q+1}h_* e⁻¹F` of an
  abelian sheaf annihilated by `n` is injective.
* `Stacks.EtaleCohomology.mono_cokernelMap_higherBaseChangeMapAb_app_of_annihilated` —
  **part (2) of [Stacks, Tag 0F03]**: for `F ⊂ G` with `G` annihilated by `n`, the induced map
  of the two cokernels is injective.
* `Stacks.EtaleCohomology.mono_cokernelDesc_higherBaseChangeMapAb_app_of_injective` —
  **part (3) of [Stacks, Tag 0F03]**: when `G` is an injective sheaf of `ℤ/nℤ`-modules, the
  cokernel of the base change map of `F` sits inside `R^{q+1}h_* e⁻¹G`.
* `Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_injective` and
  `Stacks.EtaleCohomology.mono_cokernelMap_higherBaseChangeMapAb_app_of_injective` — parts (1)
  and (2) with the embedding into an injective sheaf of `ℤ/nℤ`-modules supplied by the caller;
  the two tagged statements are these at the embedding constructed here.

## Implementation notes

**Where the short exact sequence comes from.** Only the monomorphism is constructed: the
sequence is the monomorphism together with its cokernel, which is short exact in any abelian
category (`Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π`). Nothing has to be known
about the cokernel beyond its being a quotient, because annihilation by `n` is inherited by
quotients (`Stacks.Cohomology.ZModSheaf.zsmul_eq_zero_of_epi`): the forgetful functor to
abelian sheaves is therefore only needed to be *left* exact, which it is by
`AlgebraicGeometry.SheafOfModules.toSheaf_preservesLimits`, and no description of the sections
of a cokernel of abelian sheaves intervenes.

**Three universes of the small étale site.** The objects of `T.Etale` form a `Type (u + 1)` and
its morphisms a `Type u`, so every coefficient category here sits in universe `u + 1`, which is
the `max` of the two. That is what the instances at the head of the file record, each with its
universe arguments written out: `Stacks.SheafifyCommRing.hasSheafifyCommRingCat` and
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` are stated with the coefficient
universe a `max`, and that `max` does not unify with `u + 1` by instance search alone.

**Why the injective hull is never named.** The hull is spelled `Injective.under
(torsionEtaleModule F hF)` wherever it occurs rather than abbreviated by a definition of its
own. Instance search runs at reducible transparency, so with an abbreviation `H F hF` in the
statement the monomorphy of `Injective.ι (torsionEtaleModule F hF) : _ ⟶ H F hF` is not found:
`Injective.ι_mono` concludes monomorphy at the target `Injective.under _`, and unfolding `H` to
match it is a step instance search does not take.

**Why `Z` is supplied explicitly at every call.** The three assertions of `LadderAssembly` take
the short exact sequence as an implicit argument `Z` and conclude about `Z.X₁`. Leaving it to
be solved from the conclusion poses the unification problem `?Z.X₁ =?= F` with `?Z` a
metavariable, which at these concrete sheaf categories exhausts the heartbeat budget in `whnf`;
passing `Z := ShortComplex.mk k (cokernel.π k) (cokernel.condition k)` by name makes every
projection a structure projection and the elaboration immediate.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.Cohomology.BaseChange

/-- **A monomorphism and its cokernel form a short exact sequence.** This is the only way a
short exact sequence is produced below: the quotient term is never described, only used. -/
public theorem shortExact_mk_cokernel_π {A : Type*} [Category* A] [Abelian A] {F I : A}
    (ψ : F ⟶ I) [Mono ψ] :
    (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ))
    inferInstance inferInstance

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

/-! ### The constant sheaf of rings `ℤ/nℤ` on the small étale site -/

section RingSheaf

variable (T : Scheme.{u}) (n : ℤ)

/-- Sheafification of presheaves of commutative rings exists, and is left exact, on the small
étale site of a scheme, with the rings in the universe `u + 1` of the objects of the site. -/
public instance hasSheafifyCommRingCat_smallEtale :
    HasSheafify (smallEtaleTopology T) CommRingCat.{u + 1} :=
  Stacks.SheafifyCommRing.hasSheafifyCommRingCat.{u, u, u + 1} (smallEtaleTopology T)

/-- Sheafification of presheaves of commutative rings on the small étale site of a scheme
inverts exactly the locally bijective maps. -/
public instance wEqualsLocallyBijective_commRingCat_smallEtale :
    (smallEtaleTopology T).WEqualsLocallyBijective CommRingCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.mk' _ _

/-- **The constant sheaf of rings `ℤ/nℤ` on the small étale site of `T`.** Only `|n|` enters,
`ℤ/nℤ` and `ℤ/(-n)ℤ` being the same ring; `n = 0` is allowed, `ZMod 0` being `ℤ`. -/
@[sga "7 XXII 2.0" "partial"]
public def etaleZModRingSheaf : Sheaf (smallEtaleTopology T) RingCat.{u + 1} :=
  zmodRingSheaf.{u + 1} (smallEtaleTopology T) n.natAbs

/-- **Sheaves of `ℤ/nℤ`-modules on the small étale site of `T` have enough injectives.** This
is the existence half of the choice made by [Stacks, Tag 0F03]. -/
public instance enoughInjectives_etaleZModModules :
    EnoughInjectives (SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u + 1, u} _

/-- **The sections of the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules on the small
étale site of `T` are annihilated by `n`.** This is what makes the middle and right terms of
the sequence of [Stacks, Tag 0F03] available to a statement about `n`-torsion sheaves. -/
public theorem zsmul_toSheaf_etaleZModRingSheaf_eq_zero
    (M : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) (U : T.Etale)
    (x : ((SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj M).obj.obj (op U)) :
    n • x = 0 :=
  (natAbs_nsmul_eq_zero_iff n x).1
    (nsmul_toSheaf_eq_zero.{u + 1, u + 1} (smallEtaleTopology T) n.natAbs M (op U) x)

end RingSheaf

/-! ### The embedding of an abelian sheaf annihilated by `n` -/

section Embedding

variable {T : Scheme.{u}} {n : ℤ} (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
  (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)

/-- An abelian sheaf on the small étale site of `T` annihilated by `n`, read as a sheaf of
`ℤ/nℤ`-modules: the sectionwise `ℤ/nℤ`-action, sheafified. -/
public def torsionEtaleModule : SheafOfModules.{u + 1} (etaleZModRingSheaf T n) :=
  torsionSheafToModules.{u + 1, u + 1} (smallEtaleTopology T) n.natAbs F
    (fun X x ↦ (natAbs_nsmul_eq_zero_iff n x).2 (hF X.unop x))

/-- The underlying abelian sheaf of `torsionEtaleModule F hF` is `F` itself. -/
public def torsionEtaleModuleIso :
    (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj
        (torsionEtaleModule F hF) ≅ F :=
  torsionSheafToModulesIso.{u + 1, u + 1} (smallEtaleTopology T) n.natAbs F _

/-- **The embedding of [Stacks, Tag 0F03]**: an abelian sheaf on the small étale site of `T`
annihilated by `n` sits inside the underlying abelian sheaf of an injective sheaf of
`ℤ/nℤ`-modules. It is `F`, read as a sheaf of `ℤ/nℤ`-modules, inside an injective hull of the
latter. -/
public def torsionEtaleInjectiveEmbedding :
    F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj
      (Injective.under (torsionEtaleModule F hF)) :=
  (torsionEtaleModuleIso F hF).inv ≫
    (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).map
      (Injective.ι (torsionEtaleModule F hF))

/-- The embedding of [Stacks, Tag 0F03] is a monomorphism: it is an isomorphism followed by the
image under the left exact forgetful functor of the inclusion into an injective hull. -/
public instance mono_torsionEtaleInjectiveEmbedding :
    Mono (torsionEtaleInjectiveEmbedding F hF) :=
  mono_comp _ _

end Embedding

/-! ### The three assertions of [Stacks, Tag 0F03], given an embedding -/

section Assertions

variable {X S S' X' T Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
  (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)

/-- The composite of the base change map of `F` with `R^{q+1}h_* e⁻¹(F ⟶ I)` vanishes when `I`
is an injective sheaf of `ℤ/nℤ`-modules, so that the cokernel of the base change map of `F`
maps canonically to `R^{q+1}h_* e⁻¹I`. This is
`higherBaseChangeMapAb_app_comp_map_eq_zero` with its comparison ladder constructed. -/
public theorem higherBaseChangeMapAb_app_comp_map_eq_zero_of_injective
    (sq : IsPullback h e f' g) {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) [Injective I]
    (k : F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I) (hk : Mono k) :
    (higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F ≫
      (higherBaseChangeTarget h e (q + 1)).map k = 0 :=
  have := hk
  higherBaseChangeMapAb_app_comp_map_eq_zero q f' g h e sq k (cokernel.π k)
    (higherBaseChangeLadder f' g h e sq.w q
      (Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π k)
      (isZero_higherBaseChangeSource_toSheaf_succ f' g (etaleZModRingSheaf T n) I q))

/-- The cokernel of a map into the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules is
annihilated by `n`, being a quotient of it. -/
private theorem zsmul_cokernel_eq_zero_of_modules
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n))
    {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (k : F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I)
    (U : T.Etale) (x : (cokernel k).obj.obj (op U)) : n • x = 0 :=
  zsmul_eq_zero_of_epi (cokernel.π k) n
    (fun Z y ↦ zsmul_toSheaf_etaleZModRingSheaf_eq_zero T n I Z.unop y) (op U) x

/-- **Part (1) of [Stacks, Tag 0F03], given an embedding of `F` into an injective sheaf of
`ℤ/nℤ`-modules.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q)`, let

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

be a commutative diagram with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and let `F` on the small étale site of `T` be annihilated by `n` and contained
in the underlying abelian sheaf of an injective sheaf `I` of `ℤ/nℤ`-modules. Then the base
change map `(f')⁻¹R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹F` is injective.

The short exact sequence of the source is `F ⊂ I` together with its cokernel; `I` is
annihilated by `n` because it is a sheaf of `ℤ/nℤ`-modules, hence so is the cokernel, and
`(f')⁻¹R^{q+1} g_*` vanishes on `I` because it is injective. -/
public theorem mono_higherBaseChangeMapAb_app_of_injective
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) [Injective I]
    (k : F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I) (hk : Mono k) :
    Mono ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) := by
  have := hk
  have hI := zsmul_toSheaf_etaleZModRingSheaf_eq_zero T n I
  have hQ := zsmul_cokernel_eq_zero_of_modules n I k
  exact mono_higherBaseChangeMapAb_app_of_shortExact f n q s p f' g h e hbc sq₁ sq
    (Z := ShortComplex.mk k (cokernel.π k) (cokernel.condition k))
    (Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π k)
    (isZero_higherBaseChangeSource_toSheaf_succ f' g (etaleZModRingSheaf T n) I q) hF hI hQ

/-- **Part (3) of [Stacks, Tag 0F03].** In the situation of
`mono_higherBaseChangeMapAb_app_of_injective`, with `F` annihilated by `n` contained in the
underlying abelian sheaf of an injective sheaf `I` of `ℤ/nℤ`-modules,

`Coker((f')⁻¹R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹F) ⊂ R^{q+1} h_* e⁻¹I`,

the inclusion being the canonical map induced by `R^{q+1}h_* e⁻¹(F ⟶ I)`, which is defined
because `higherBaseChangeMapAb_app_comp_map_eq_zero_of_injective` vanishes. This is
`mono_cokernelDesc_higherBaseChangeMapAb_app_of_shortExact` with its short exact sequence
constructed from `F ⊂ I`. -/
@[stacks 0F03 "part (3), the cokernel inside R^q h_* e⁻¹ of an injective ℤ/nℤ-module sheaf"]
public theorem mono_cokernelDesc_higherBaseChangeMapAb_app_of_injective
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) [Injective I]
    (k : F ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I) (hk : Mono k) :
    Mono (cokernel.desc ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeTarget h e (q + 1)).map k)
      (higherBaseChangeMapAb_app_comp_map_eq_zero_of_injective n q f' g h e sq I k hk)) := by
  have := hk
  have hI := zsmul_toSheaf_etaleZModRingSheaf_eq_zero T n I
  have hQ := zsmul_cokernel_eq_zero_of_modules n I k
  exact mono_cokernelDesc_higherBaseChangeMapAb_app_of_shortExact f n q s p f' g h e hbc sq₁ sq
    (Z := ShortComplex.mk k (cokernel.π k) (cokernel.condition k))
    (Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π k)
    (isZero_higherBaseChangeSource_toSheaf_succ f' g (etaleZModRingSheaf T n) I q) hF hI hQ

/-- **Part (2) of [Stacks, Tag 0F03], given an embedding of `G` into an injective sheaf of
`ℤ/nℤ`-modules.** In the situation of `mono_higherBaseChangeMapAb_app_of_injective`, if
`F ⊂ G` with `F` and `G` annihilated by `n` and `G` contained in the underlying abelian sheaf
of an injective sheaf `I` of `ℤ/nℤ`-modules, then

`Coker((f')⁻¹R^{q+1}g_* F → R^{q+1}h_* e⁻¹F) ⊂ Coker((f')⁻¹R^{q+1}g_* G → R^{q+1}h_* e⁻¹G)`,

the inclusion being the map induced on cokernels by the naturality square of the base change
map. The two short exact sequences of the source are `F ⊂ I` and `G ⊂ I`, with the same middle
term, together with their cokernels; this is the choice `F ⊂ G ⊂ I` of the source. -/
public theorem mono_cokernelMap_higherBaseChangeMapAb_app_of_injective
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F G : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (i : F ⟶ G) (hi : Mono i)
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hG : ∀ (U : T.Etale) (x : G.obj.obj (op U)), n • x = 0)
    (I : SheafOfModules.{u + 1} (etaleZModRingSheaf T n)) [Injective I]
    (k : G ⟶ (SheafOfModules.toSheaf.{u + 1} (etaleZModRingSheaf T n)).obj I) (hk : Mono k) :
    Mono (cokernel.map ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app G)
      ((higherBaseChangeSource f' g (q + 1)).map i)
      ((higherBaseChangeTarget h e (q + 1)).map i)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).naturality i).symm) := by
  have := hi
  have := hk
  have hI := zsmul_toSheaf_etaleZModRingSheaf_eq_zero T n I
  have hQF := zsmul_cokernel_eq_zero_of_modules n I (i ≫ k)
  have hQG := zsmul_cokernel_eq_zero_of_modules n I k
  exact mono_cokernelMap_higherBaseChangeMapAb_app_of_shortExact f n q s p f' g h e hbc sq₁ sq
    i k (cokernel.π (i ≫ k)) (cokernel.π k) hi
    (hzF := cokernel.condition (i ≫ k)) (hzG := cokernel.condition k)
    (Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π (i ≫ k))
    (Stacks.Cohomology.BaseChange.shortExact_mk_cokernel_π k)
    (isZero_higherBaseChangeSource_toSheaf_succ f' g (etaleZModRingSheaf T n) I q)
    hF hG hI hQF hQG

/-! ### The three assertions of [Stacks, Tag 0F03] -/

/-- **Part (1) of [Stacks, Tag 0F03].** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02],
assume `BC(f, n, q)`, let

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

be a commutative diagram with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and let `F` be an abelian sheaf on the small étale site of `T` annihilated
by `n`. Then the base change map `(f')⁻¹R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹F` is injective.

This is `mono_higherBaseChangeMapAb_app_of_injective` at the embedding
`torsionEtaleInjectiveEmbedding` of `F` into an injective sheaf of `ℤ/nℤ`-modules. -/
@[stacks 0F03 "part (1), injectivity of the base change map"]
public theorem mono_higherBaseChangeMapAb_app_of_annihilated
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) :
    Mono ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) :=
  mono_higherBaseChangeMapAb_app_of_injective f n q s p f' g h e hbc sq₁ sq hF
    (Injective.under (torsionEtaleModule F hF)) (torsionEtaleInjectiveEmbedding F hF)
    (mono_torsionEtaleInjectiveEmbedding F hF)

/-- **Part (2) of [Stacks, Tag 0F03].** In the situation of
`mono_higherBaseChangeMapAb_app_of_annihilated`, if `F ⊂ G` where `G` on the small étale site
of `T` is annihilated by `n`, then

`Coker((f')⁻¹R^{q+1}g_* F → R^{q+1}h_* e⁻¹F) ⊂ Coker((f')⁻¹R^{q+1}g_* G → R^{q+1}h_* e⁻¹G)`,

the inclusion being the map induced on cokernels by the naturality square of the base change
map. This is `mono_cokernelMap_higherBaseChangeMapAb_app_of_injective` at the embedding
`torsionEtaleInjectiveEmbedding` of `G` into an injective sheaf of `ℤ/nℤ`-modules, which
realises the choice `F ⊂ G ⊂ I` of the source. -/
@[stacks 0F03 "part (2), the cokernel inclusion under F ⊂ G"]
public theorem mono_cokernelMap_higherBaseChangeMapAb_app_of_annihilated
    (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F G : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (i : F ⟶ G) (hi : Mono i)
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hG : ∀ (U : T.Etale) (x : G.obj.obj (op U)), n • x = 0) :
    Mono (cokernel.map ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app G)
      ((higherBaseChangeSource f' g (q + 1)).map i)
      ((higherBaseChangeTarget h e (q + 1)).map i)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).naturality i).symm) :=
  mono_cokernelMap_higherBaseChangeMapAb_app_of_injective f n q s p f' g h e hbc sq₁ sq i hi
    hF hG (Injective.under (torsionEtaleModule G hG)) (torsionEtaleInjectiveEmbedding G hG)
    (mono_torsionEtaleInjectiveEmbedding G hG)

end Assertions

end Stacks.EtaleCohomology

end
