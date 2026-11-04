module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelFirstOrderBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelThickeningRingHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeBijective

/-!
# The small-site/big-site bridge for the first-order base change of sections

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `(U, T, δ)` of the small
crystalline site `Cris(X/S)`.  [Stacks, Tag 07J2] gives the first-order thickening `(U, T', δ')`
of that object together with the two projections `p₀, p₁ : T' ⟶ T`, and the base change of
sections along `p₀`,

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ) ⟶ Γ(T', ℱ)`,  `t ⊗ s ↦ t · p₀^* s`,

is written twice in the tree: for a sheaf of modules on the big site `CRIS(X/S)` as
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, whose bijectivity is reduced to the
affine chain of `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean`, and for a
sheaf of modules on the small site `Cris(X/S)` as
`...SmallSite.crysExtensionSectionsMap`, which is the spelling the level datum of
[Stacks, Lemma 60.17.3, Tag 07JG] consumes.  **This module identifies the two**, and transports
bijectivity from the big site to the small one.

## The identification is an identity, not an isomorphism

The small-site map is written at an object `B` of `Cris(X/S)` but every ring and every object
appearing in it is already a big-site one: the scalars are
`Crystalline.GlobalCrystallineSituation.crysSheafRing` at `B.obj` and at
`...firstOrderThickeningObject S B.obj`, the target object is
`...firstOrderThickeningCrysObject S B`, which is `...firstOrderThickeningObject S B.obj` carrying
the open-immersion property of `B`, and the restriction map is the small-site map of
`...firstOrderThickeningCrysP₀ S B`, which is `...firstOrderThickeningSiteP₀ S B.obj` carrying no
extra data.  Only the sheaf differs: one lives on `Cris(X/S)` and the other on `CRIS(X/S)`.

`...SmallSite.restrictSheafOfModules` takes a sheaf of modules on `CRIS(X/S)` to one on
`Cris(X/S)` by restriction along the inclusion `i : Cris(X/S) ⥤ CRIS(X/S)`, with **no** restriction
of scalars — the structure sheaf of the small site is the restriction of that of the big one on the
nose, `...SmallSite.crisRing` being `(CrystallineThickening.ι S).op ⋙ ...crisRing S` — so the
sections, their scalars and their restriction maps are untouched.  Consequently the two base-change
maps are not merely isomorphic: for `N` on `CRIS(X/S)` the two maps have the same source, the same
target and the same values, `crysExtensionSectionsMap_restrictSheafOfModules`, and bijectivity of
one *is* bijectivity of the other.

Nothing here routes through the lower shriek `i_!` on modules, which is not exact
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`); nor through `i_*`, which at module
coefficients only exists at the raised universe `u + 1` of
`...SmallSite.ModuleSheaf` because its value is a limit indexed by the objects of the site, whereas
both base-change maps are written for modules with sections in `Type u`.  Plain restriction is
available at `Type u`, and it is all that is used.

## Transport along an isomorphism

A general sheaf of modules on `Cris(X/S)` is not *literally* the restriction of one on
`CRIS(X/S)`, so the identity above is paired with a transport along an isomorphism of sheaves of
modules on the small site: `bijective_crysExtensionSectionsMap_congr`.  The two together give
`bijective_crysExtensionSectionsMap_of_restrictIso`, the form in which the big-site statement
composes with the level datum of [Stacks, Tag 07JG].

## Main definitions

* `crysSectionsEquivOfIso` — the sections of isomorphic sheaves of modules on `Cris(X/S)` over an
  object, as a linear equivalence over the sections of the structure sheaf there.
* `crysExtensionSourceEquivOfIso` — the induced equivalence of the sources of the two base-change
  maps, `𝟙 ⊗ crysSectionsEquivOfIso`.

## Main results

* `crysExtensionSectionsMap_restrictSheafOfModules` — **the two base-change maps agree**: the
  small-site map of the restriction of a sheaf of modules on `CRIS(X/S)` is the big-site map of
  that sheaf at the underlying object.
* `bijective_crysExtensionSectionsMap_restrictSheafOfModules_iff` — hence the two bijectivity
  statements are the same statement.
* `crysExtensionSectionsMap_crysSectionsEquivOfIso` — the square expressing that the base-change
  map is natural in the sheaf.
* `bijective_crysExtensionSectionsMap_congr` — **bijectivity of the small-site base-change map
  depends only on the isomorphism class of the sheaf.**
* `bijective_crysExtensionSectionsMap_iff_of_sectionsEquiv` — **the pointwise transport**: two
  sheaves of modules on `Cris(X/S)` whose sections are identified over the object and over its
  first-order thickening, compatibly with the two restrictions along `p₀`, have bijective
  base-change map together.  Neither an isomorphism of sheaves nor any condition elsewhere on the
  site is asked for.
* `bijective_crysExtensionSectionsMap_iff_of_bigSectionsEquiv` — the same across the two sites:
  the small-site map of `ℱ` at `B` and the big-site map of `N` at the underlying object are
  bijective together.
* `bijective_crysExtensionSectionsMap_of_sectionsEquiv` — **the bridge from the sections alone**:
  a sheaf of modules on `CRIS(X/S)` whose sections agree with those of the given sheaf on
  `Cris(X/S)` over the object and over its first-order thickening, compatibly with the two
  restrictions along `p₀`, transports its big-site bijectivity.  No isomorphism of sheaves is
  asked for, and no condition is imposed on either sheaf elsewhere on its site.
* `bijective_crysExtensionSectionsMap_of_restrictIso` — **the bridge**: a sheaf of modules on
  `Cris(X/S)` isomorphic to the restriction of one on `CRIS(X/S)` whose big-site base-change map
  at the underlying object is bijective has bijective small-site base-change map.
* `bijective_levelExtensionSectionsMap_of_restrictIso` — the same statement in the spelling of the
  field `...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap`.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module and no tag is proved**: a change of spelling
between the two crystalline sites is not a step of any tag.

Bijectivity of either base-change map is **not** proved here: everything below is an implication
from bijectivity of the big-site map, which
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` proves for a crystal on an
object with affine ambient scheme and quasi-coherent `F_T`.  The second hypothesis of
`bijective_crysExtensionSectionsMap_of_restrictIso`, that the given sheaf on `Cris(X/S)` is
isomorphic to the restriction of one on `CRIS(X/S)`, is also not supplied here and is not supplied
anywhere: for a crystal in quasi-coherent modules it is essential surjectivity of
`...SmallSite.restrictSheafOfModules` on crystals, and
`SmallSite/BigSiteLift.lean` proves that lift at the module universe `u + 1` of
`...SmallSite.ModuleSheaf`, where the direct image `i_*` of modules lives, and states exactly what
the lift at the module universe `u` of these base-change maps would be.  What this module removes
is the change of sites, and that is all it claims to remove.

The change of sites is **not** the only route to the small-site statement, and it is no longer the
one the chapter takes.  `SmallSite/CrysFirstOrderAffineBaseChange.lean` proves
`...SmallSite.bijective_crysExtensionSectionsMap` — the small-site base-change map of a crystal
over an object with affine ambient scheme and quasi-coherent `ℱ_T` is bijective — directly on
`Cris(X/S)`, with no sheaf on `CRIS(X/S)` anywhere, and
`SmallSite/LevelBaseChangeAffineLevels.lean` discharges with it the field of
[Stacks, Lemma 60.17.3, Tag 07JG] that `SmallSite/LevelBaseChangeFromBigSite.lean` reduces to a
lift.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The two base-change maps are one map -/

section Restrict

variable (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (B : CrystallineThickening S)

/-- **Restriction along `p₀` on the small site, for a sheaf of modules restricted from the big
site, is restriction along `p₀` on the big site.**  The morphism `p₀` of `Cris(X/S)` is the
morphism `p₀` of `CRIS(X/S)` between the underlying objects, and restriction along the inclusion
leaves the sections and their restriction maps untouched. -/
theorem crysSectionsP₀_restrictSheafOfModules (s : (restrictSheafOfModules N).val.obj (op B)) :
    crysSectionsP₀ (restrictSheafOfModules N) B s =
      moduleSiteRestrict N (firstOrderThickeningSiteP₀ S B.obj) s :=
  rfl

/-- The bilinear datum of the small-site base change of a sheaf of modules restricted from the big
site is the bilinear datum of the big-site base change. -/
theorem crysExtensionSectionsAux_restrictSheafOfModules :
    crysExtensionSectionsAux (restrictSheafOfModules N) B = extensionSectionsAux N B.obj :=
  rfl

/-- **The small-site base change of sections of a sheaf of modules restricted from `CRIS(X/S)` is
the big-site base change of that sheaf at the underlying object.**

Both are the map `Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, ℱ) ⟶ Γ(T', ℱ)`, `t ⊗ s ↦ t · p₀^* s`, of
[Stacks, Tag 07J2]; the two rings, the two tensor products, the target and the restriction along
`p₀` all agree on the nose, the structure sheaf of `Cris(X/S)` being the restriction of that of
`CRIS(X/S)` along the inclusion and `...SmallSite.restrictSheafOfModules` performing no restriction
of scalars. -/
theorem crysExtensionSectionsMap_restrictSheafOfModules :
    crysExtensionSectionsMap (restrictSheafOfModules N) B = extensionSectionsMap N B.obj :=
  rfl

/-- **Bijectivity of the small-site base change of a restricted sheaf of modules is bijectivity of
the big-site base change**, the two maps being the same map. -/
theorem bijective_crysExtensionSectionsMap_restrictSheafOfModules_iff :
    Function.Bijective (crysExtensionSectionsMap (restrictSheafOfModules N) B) ↔
      Function.Bijective (extensionSectionsMap N ((CrystallineThickening.ι S).obj B)) :=
  Iff.rfl

/-- **The bridge for a restricted sheaf of modules**: bijectivity of the big-site base change of
`N` at the object underlying `B` gives bijectivity of the small-site base change of the
restriction of `N` to `Cris(X/S)` at `B`. -/
theorem bijective_crysExtensionSectionsMap_restrictSheafOfModules
    (h : Function.Bijective (extensionSectionsMap N ((CrystallineThickening.ι S).obj B))) :
    Function.Bijective (crysExtensionSectionsMap (restrictSheafOfModules N) B) :=
  h

end Restrict

/-- The base change of sections commutes with a pair of linear equivalences of sections that are
compatible with the restrictions along `p₀`, on a pure tensor. -/
private theorem crysExtensionSectionsMap_tmul_comm {F F' : SheafOfModules.{u} (structureSheaf S)}
    (B : CrystallineThickening S)
    (φ₀ : F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj] F'.val.obj (op B))
    (φ₁ : F.val.obj (op (firstOrderThickeningCrysObject S B))
      ≃ₗ[crysSheafRing S (firstOrderThickeningObject S B.obj)]
      F'.val.obj (op (firstOrderThickeningCrysObject S B)))
    (hcomm : ∀ s : F.val.obj (op B), φ₁ (crysSectionsP₀ F B s) = crysSectionsP₀ F' B (φ₀ s))
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysExtensionSectionsMap F' B (t ⊗ₜ[crysSheafRing S B.obj] φ₀ s) =
      φ₁ (crysExtensionSectionsMap F B (t ⊗ₜ[crysSheafRing S B.obj] s)) := by
  rw [crysExtensionSectionsMap_tmul, crysExtensionSectionsMap_tmul, map_smul, hcomm]

/-! ### Transport along an isomorphism of sheaves of modules -/

section Congr

variable {F F' : SheafOfModules.{u} (structureSheaf S)}

/-- **The sections of isomorphic sheaves of modules on `Cris(X/S)` over an object of the site**,
as a linear equivalence over the ring `Γ(T, 𝒪_T)` of sections of the structure sheaf there. -/
def crysSectionsEquivOfIso (e : F ≅ F') (B : CrystallineThickening S) :
    F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj] F'.val.obj (op B) :=
  ((SheafOfModules.evaluation (structureSheaf S) (op B)).mapIso e).toLinearEquiv

/-- The equivalence of sections of an isomorphism is the isomorphism, on sections. -/
@[simp]
theorem crysSectionsEquivOfIso_apply (e : F ≅ F') (B : CrystallineThickening S)
    (s : F.val.obj (op B)) :
    crysSectionsEquivOfIso e B s = e.hom.val.app (op B) s :=
  rfl

/-- **The equivalence of sections is compatible with the restriction maps of the site**, being the
value of a morphism of presheaves of modules. -/
theorem crysSectionsEquivOfIso_naturality (e : F ≅ F') {A B : CrystallineThickening S}
    (g : A ⟶ B) (s : F.val.obj (op B)) :
    crysSectionsEquivOfIso e A (F.val.map g.op s) =
      F'.val.map g.op (crysSectionsEquivOfIso e B s) :=
  PresheafOfModules.naturality_apply e.hom.val g.op s

/-- **The source of the small-site base-change map, transported along an isomorphism of sheaves of
modules**: the identity of `Γ(T', 𝒪_{T'})` tensored with `crysSectionsEquivOfIso`. -/
def crysExtensionSourceEquivOfIso (e : F ≅ F') (B : CrystallineThickening S) :
    crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj]
      crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
        F'.val.obj (op B) :=
  TensorProduct.congr (LinearEquiv.refl _ _) (crysSectionsEquivOfIso e B)

/-- The transported source of the base-change map, on a pure tensor. -/
@[simp]
theorem crysExtensionSourceEquivOfIso_tmul (e : F ≅ F') (B : CrystallineThickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S B.obj)) (s : F.val.obj (op B)) :
    crysExtensionSourceEquivOfIso e B (t ⊗ₜ[crysSheafRing S B.obj] s) =
      t ⊗ₜ[crysSheafRing S B.obj] crysSectionsEquivOfIso e B s :=
  TensorProduct.congr_tmul _ _ _ _

/-- **The small-site base change of sections is natural in the sheaf of modules**: transporting a
tensor along an isomorphism and then base changing is base changing and then transporting the
resulting section over the first-order thickening. -/
theorem crysExtensionSectionsMap_crysSectionsEquivOfIso (e : F ≅ F')
    (B : CrystallineThickening S)
    (z : crysSheafRing S (firstOrderThickeningObject S B.obj) ⊗[crysSheafRing S B.obj]
      F.val.obj (op B)) :
    crysExtensionSectionsMap F' B (crysExtensionSourceEquivOfIso e B z) =
      crysSectionsEquivOfIso e (firstOrderThickeningCrysObject S B)
        (crysExtensionSectionsMap F B z) :=
  TensorProduct.apply_lTensor_of_tmul_comm (e := crysSectionsEquivOfIso e B)
    (e₁ := (crysSectionsEquivOfIso e (firstOrderThickeningCrysObject S B)).toAddEquiv)
    (crysExtensionSectionsMap_tmul_comm B _ _
      (crysSectionsEquivOfIso_naturality e (firstOrderThickeningCrysP₀ S B))) z

/-- **Bijectivity of the small-site base change of sections depends only on the isomorphism class
of the sheaf of modules.**  The source and the target of the map are each transported by a linear
equivalence, compatibly with the map. -/
theorem bijective_crysExtensionSectionsMap_of_iso (e : F ≅ F') (B : CrystallineThickening S)
    (h : Function.Bijective (crysExtensionSectionsMap F B)) :
    Function.Bijective (crysExtensionSectionsMap F' B) :=
  (TensorProduct.bijective_iff_of_tmul_comm (crysSectionsEquivOfIso e B)
    (crysSectionsEquivOfIso e (firstOrderThickeningCrysObject S B)).toAddEquiv
    (crysExtensionSectionsMap_tmul_comm B _ _
      (crysSectionsEquivOfIso_naturality e (firstOrderThickeningCrysP₀ S B)))).mp h

/-- **Bijectivity of the small-site base change of sections is an invariant of the isomorphism
class of the sheaf of modules.** -/
theorem bijective_crysExtensionSectionsMap_congr (e : F ≅ F') (B : CrystallineThickening S) :
    Function.Bijective (crysExtensionSectionsMap F B) ↔
      Function.Bijective (crysExtensionSectionsMap F' B) :=
  ⟨bijective_crysExtensionSectionsMap_of_iso e B,
    bijective_crysExtensionSectionsMap_of_iso e.symm B⟩

end Congr

/-! ### The pointwise transport -/

section Pointwise

/-- **The pointwise transport of the small-site base change of sections.**

Bijectivity of `...SmallSite.crysExtensionSectionsMap` at an object `B = (U, T, δ)` reads the
sheaf of modules at `B`, at the first-order thickening `(U, T', δ')` of [Stacks, Tag 07J2], and
along the restriction `p₀` between them, and nowhere else.  So two sheaves of modules on
`Cris(X/S)` whose sections are identified over those two objects — linearly over the section ring
of each, compatibly with the two restrictions along `p₀` — have bijective base change together.

No isomorphism of sheaves is asked for and nothing is assumed about either sheaf anywhere else on
the site, which is what makes this more general than `bijective_crysExtensionSectionsMap_congr`:
that is this statement with the two identifications read off an isomorphism.  The transport is
`TensorProduct.bijective_iff_of_tmul_comm`, the identification of the sections over `B` extending
to the base change that is the source of the map. -/
theorem bijective_crysExtensionSectionsMap_iff_of_sectionsEquiv
    {F F' : SheafOfModules.{u} (structureSheaf S)} (B : CrystallineThickening S)
    (φ₀ : F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj] F'.val.obj (op B))
    (φ₁ : F.val.obj (op (firstOrderThickeningCrysObject S B))
      ≃ₗ[crysSheafRing S (firstOrderThickeningObject S B.obj)]
      F'.val.obj (op (firstOrderThickeningCrysObject S B)))
    (hcomm : ∀ s : F.val.obj (op B), φ₁ (crysSectionsP₀ F B s) = crysSectionsP₀ F' B (φ₀ s)) :
    Function.Bijective (crysExtensionSectionsMap F B) ↔
      Function.Bijective (crysExtensionSectionsMap F' B) :=
  TensorProduct.bijective_iff_of_tmul_comm φ₀ φ₁.toAddEquiv
    (crysExtensionSectionsMap_tmul_comm B φ₀ φ₁ hcomm)

/-- **The pointwise transport across the two sites.**

For a sheaf of modules `ℱ` on `Cris(X/S)` and one `N` on `CRIS(X/S)` the small-site base change
of `ℱ` at `B` and the big-site base change of `N` at the underlying object are bijective
together, as soon as the sections of the two are identified over `B` and over its first-order
thickening, compatibly with the two restrictions along `p₀`.

It is the previous statement at `F' = ...SmallSite.restrictSheafOfModules N`, whose sections,
scalars and restriction maps are those of `N` on the nose, together with
`crysExtensionSectionsMap_restrictSheafOfModules`. -/
theorem bijective_crysExtensionSectionsMap_iff_of_bigSectionsEquiv
    {F : SheafOfModules.{u} (structureSheaf S)}
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (B : CrystallineThickening S)
    (φ₀ : F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj] N.val.obj (op B.obj))
    (φ₁ : F.val.obj (op (firstOrderThickeningCrysObject S B))
      ≃ₗ[crysSheafRing S (firstOrderThickeningObject S B.obj)]
      N.val.obj (op (firstOrderThickeningObject S B.obj)))
    (hcomm : ∀ s : F.val.obj (op B), φ₁ (crysSectionsP₀ F B s) =
      moduleSiteRestrict N (firstOrderThickeningSiteP₀ S B.obj) (φ₀ s)) :
    Function.Bijective (crysExtensionSectionsMap F B) ↔
      Function.Bijective (extensionSectionsMap N ((CrystallineThickening.ι S).obj B)) :=
  bijective_crysExtensionSectionsMap_iff_of_sectionsEquiv (F' := restrictSheafOfModules N) B φ₀ φ₁
    hcomm

end Pointwise

/-! ### The bridge from two identifications of sections -/

/-- **The bridge, from the sections alone.**

What bijectivity of the small-site base change at `B` depends on is the sheaf `ℱ` on `Cris(X/S)`
at the two objects `B` and its first-order thickening, and the restriction along `p₀` between them.
So a sheaf `N` on `CRIS(X/S)` transports its big-site bijectivity to `ℱ` as soon as the sections of
the two agree over those two objects — linearly over the section ring of each, compatibly with the
two restrictions along `p₀`.  No isomorphism of sheaves is needed, and nothing is assumed about
either sheaf anywhere else on its site.

It is one direction of `bijective_crysExtensionSectionsMap_iff_of_bigSectionsEquiv`, the form in
which the two identifications are compared;
`bijective_crysExtensionSectionsMap_of_restrictIso` is the form in which an isomorphism of
sheaves of modules supplies them. -/
theorem bijective_crysExtensionSectionsMap_of_sectionsEquiv
    {F : SheafOfModules.{u} (structureSheaf S)}
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (B : CrystallineThickening S)
    (φ₀ : F.val.obj (op B) ≃ₗ[crysSheafRing S B.obj] N.val.obj (op B.obj))
    (φ₁ : F.val.obj (op (firstOrderThickeningCrysObject S B))
      ≃ₗ[crysSheafRing S (firstOrderThickeningObject S B.obj)]
      N.val.obj (op (firstOrderThickeningObject S B.obj)))
    (hcomm : ∀ s : F.val.obj (op B), φ₁ (crysSectionsP₀ F B s) =
      moduleSiteRestrict N (firstOrderThickeningSiteP₀ S B.obj) (φ₀ s))
    (h : Function.Bijective (extensionSectionsMap N ((CrystallineThickening.ι S).obj B))) :
    Function.Bijective (crysExtensionSectionsMap F B) :=
  (bijective_crysExtensionSectionsMap_iff_of_bigSectionsEquiv B φ₀ φ₁ hcomm).mpr h

/-! ### The bridge -/

/-- **The small-site/big-site bridge for the first-order base change of sections.**

Let `ℱ` be a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` isomorphic to the restriction of a sheaf
`N` of `𝒪_{X/S}`-modules on `CRIS(X/S)`, and let `B = (U, T, δ)` be an object of `Cris(X/S)`.  If
the big-site base change of sections of `N` along `p₀` at the underlying object of `CRIS(X/S)` is
bijective, then so is the small-site base change of sections of `ℱ` along `p₀` at `B`.

The mathematics is a change of spelling and nothing else: for the restriction of `N` the two maps
are equal, `crysExtensionSectionsMap_restrictSheafOfModules`, and bijectivity is transported along
the isomorphism by `bijective_crysExtensionSectionsMap_congr`.  Bijectivity of the big-site map is
the affine statement of [Stacks, Tag 07J6], reduced in
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` and not proved here. -/
theorem bijective_crysExtensionSectionsMap_of_restrictIso
    {F : SheafOfModules.{u} (structureSheaf S)}
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (e : restrictSheafOfModules N ≅ F)
    (B : CrystallineThickening S)
    (h : Function.Bijective (extensionSectionsMap N ((CrystallineThickening.ι S).obj B))) :
    Function.Bijective (crysExtensionSectionsMap F B) :=
  bijective_crysExtensionSectionsMap_of_iso e B
    (bijective_crysExtensionSectionsMap_restrictSheafOfModules N B h)

/-- **The bridge in the spelling the level datum of [Stacks, Lemma 60.17.3, Tag 07JG] consumes.**

`...SmallSite.LevelScalars07JG.levelExtensionSectionsMap` is the small-site base change of sections
of the crystal over the ambient object of the level, so this is exactly the field
`...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap` at one crystal and one level,
given a sheaf of modules on `CRIS(X/S)` restricting to the crystal and bijectivity of its big-site
base change at the ambient object of the level. -/
theorem bijective_levelExtensionSectionsMap_of_restrictIso {A : Type u} [CommRing A]
    {D : DividedPowerRing.{u}} (L : LevelScalars07JG S D) (F : QuasiCoherentCrystal S) (e : ℕ)
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (α : restrictSheafOfModules N ≅ F.obj)
    (h : Function.Bijective (extensionSectionsMap N (L.levelSystem.obj e).obj)) :
    Function.Bijective (L.levelExtensionSectionsMap F e) :=
  bijective_crysExtensionSectionsMap_of_restrictIso α (L.levelSystem.obj e) h

end Crystalline.GlobalCrystallineSituation.SmallSite

end
