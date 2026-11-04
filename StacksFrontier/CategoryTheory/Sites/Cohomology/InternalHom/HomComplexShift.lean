module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
import StacksCore.Tactic.StacksAttribute

/-! # Shifts of the internal Hom complex on a ringed site

Let `(C, O)` be a ringed site and let `K` and `M` be cochain complexes of `O`-modules. Their
internal Hom complex `SheafHom(K, M)` is constructed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex`, where it is characterised
by the identification of its sections over an object `U` with the ordinary Hom complex of the
restrictions `K|_U` and `M|_U`.

This file identifies the internal Hom complex of shifted complexes with a shift of the internal
Hom complex: for integers `a` and `b` there is a canonical isomorphism
`SheafHom(K, M)[a - b] ≅ SheafHom(K[b], M[a])`. It is the sheaf-theoretic form of the shift
identification of Hom complexes, built one shift at a time: shifting the source by `b` carries a
cochain to one of degree `n' = n + b` and multiplies it by the sign
`(-1)^(b n' + b (b - 1) / 2)` before reindexing, while shifting the target is sign-free.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictComplexShiftIso`: restriction to a slice site commutes
  with the shift of complexes; degreewise it is the identity.
* `AlgebraicGeometry.RingedSite.cochainSourceShiftEquiv` and
  `AlgebraicGeometry.RingedSite.cochainTargetShiftEquiv`: the shift of the source and of the
  target of a cochain between restricted complexes, as additive equivalences.
* `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso` and
  `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso`: the one-sided shift identifications
  `SheafHom(K, M)[-b] ≅ SheafHom(K[b], M)` and `SheafHom(K, M)[a] ≅ SheafHom(K, M[a])`.
* `AlgebraicGeometry.RingedSite.sheafHomShiftIso`: the two-sided identification
  `SheafHom(K, M)[a - b] ≅ SheafHom(K[b], M[a])`.

## Main results

* `AlgebraicGeometry.RingedSite.sectionsEquiv_sheafHomSourceShiftIso_hom` and
  `AlgebraicGeometry.RingedSite.sectionsEquiv_sheafHomTargetShiftIso_hom`: the two one-sided
  identifications act on sections by the corresponding shift of cochains.
* `AlgebraicGeometry.RingedSite.sectionsEquiv_sheafHomShiftIso_hom_v`: the two-sided
  identification acts on sections over `U` in degree `n` by the sign
  `(-1)^(b (n + a) + b (b - 1) / 2)` times the evident reindexing of homogeneous components.
* `AlgebraicGeometry.RingedSite.cochainSourceShift_δ` and
  `AlgebraicGeometry.RingedSite.cochainTargetShift_δ`: the differential calculations, namely
  that shifting the source by `b` and the target by `a` multiplies the Hom-complex differential
  by `(-1)^b` and by `(-1)^a` respectively.
* `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso_hom_naturality`,
  `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso_hom_naturality` and
  `AlgebraicGeometry.RingedSite.sheafHomShiftIso_hom_naturality`: each identification is natural
  in both complexes, for the functoriality
  `AlgebraicGeometry.RingedSite.homMap` of the internal Hom complex.

## Implementation notes

The internal Hom complex is only available through its characterising data, so each
identification is built from that data: on sections over `U` it is the conjugate, by
`SheafHomComplex.sectionsEquiv`, of Mathlib's shift operations `Cochain.leftShift` and
`Cochain.rightShift` on cochains. Two points make this cheap.

First, the types `Cochain (K[b])|_U L n` and `Cochain ((K|_U)[b]) L n` are definitionally equal,
because cochains depend on the complexes only through their objects and restriction to a slice
commutes with the shift on the nose in each degree; so a cochain built by `Cochain.leftShift`
may be used directly where a cochain out of the restriction of the shifted complex is wanted.
The two complexes are *not* definitionally equal, since their differentials differ by the
commutation of restriction with multiplication by `(-1)^b`; what repairs this is
`restrictComplexShiftIso`, whose components are identities and whose insertion as a zero-cochain
is absorbed by `CochainComplex.HomComplex.δ_ofHom_comp`.

Second, the signs are entirely Mathlib's: `Cochain.leftShift` already carries the sign of the
shift identification, and the factor `(-1)^b` produced by `Cochain.δ_leftShift` is exactly the
factor by which the differential of a shifted complex of sheaves differs from the original.

That each identification is a morphism of *sheaves of modules*, and not merely of sheaves of
abelian groups, is the content of the `smul_natural` field of `SheafHomComplex`, and that it is a
morphism of *complexes* is the content of `sectionsIso` being an isomorphism of complexes
together with `cochainSourceShift_δ` and `cochainTargetShift_δ`.

The universes are those of the construction of the internal Hom complex: the objects of the
site, its morphisms, the sections of the structure sheaf and the sections of the modules carry
four independent universes, and nothing here constrains them.

No attribute is placed in this file. The shift identification of Hom complexes is stated in the
source for complexes of modules over a commutative ring, and in that generality it is already
carried, with the source's own sign `(-1)^(n b)`, by
`CochainComplex.HomComplex.homComplexShiftIso` in `StacksFrontier.Homology.HomComplex.ShiftHom`.
What this file adds is the sheaf-theoretic analogue, for internal Hom complexes of complexes of
modules on a ringed site, with the signs in Mathlib's normalisation for `Cochain.leftShift`
rather than the source's. It is therefore infrastructure for the site-level theory and not a
second statement of the source's result.

## References

* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m s u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})

section Sections



/-- A unit integer multiple of a morphism of sheaves of modules acts on sections by the same
multiple. -/
private lemma unitsSmul_val_app_apply {C₀ : Type u} [Category.{v} C₀]
    {J : GrothendieckTopology C₀} {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{s} R}
    (ε : ℤˣ) (φ : A ⟶ B) (W : C₀ᵒᵖ) (x : A.val.obj W) :
    ((ε • φ).val.app W) x = ε • ((φ.val.app W) x) :=
  zsmul_val_app_apply (ε : ℤ) φ W x

/-- Two morphisms of sheaves of modules on the site agree as soon as they agree on all
sections. -/
lemma sheafHom_ext {A B : SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {φ ψ : A ⟶ B}
    (h : ∀ (U : X.C) (x : A.val.obj (op U)),
      (φ.val.app (op U)) x = (ψ.val.app (op U)) x) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun ⟨U⟩ ↦
    ModuleCat.hom_ext (LinearMap.ext (h U)))

/- `overSheafHom_ext` stood here: the same statement with the same proof as `over_hom_ext`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/HomComplexFunctoriality.lean:178`,
which this module imports. That one is the lower copy, so it is the survivor and is now
public; the four uses below name it. -/

/-- A family of maps on the sections of two sheaves of modules which is additive, linear over
the sections of the structure sheaf and compatible with restriction along arrows of the site,
as a morphism of sheaves of modules. -/
noncomputable def sheafHomOfSectionMaps
    {A B : SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (F : ∀ U : X.C, A.val.obj (op U) → B.val.obj (op U))
    (hadd : ∀ (U : X.C) (x y : A.val.obj (op U)), F U (x + y) = F U x + F U y)
    (hsmul : ∀ (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (x : A.val.obj (op U)),
      F U (r • x) = r • F U x)
    (hres : ∀ {U V : X.C} (g : V ⟶ U) (x : A.val.obj (op U)),
      F V (restrictSection X g x) = restrictSection X g (F U x)) :
    A ⟶ B :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
       { toFun := fun x ↦ F U.unop x
         map_add' := fun x y ↦ hadd U.unop x y
         map_smul' := fun r x ↦ hsmul U.unop r x }
     naturality := by
       rintro ⟨U⟩ ⟨V⟩ ⟨g : V ⟶ U⟩
       exact ModuleCat.hom_ext (LinearMap.ext (hres g)) }⟩

/-- `sheafHomOfSectionMaps` acts on sections by the given family of maps. -/
@[simp]
lemma sheafHomOfSectionMaps_val_app_apply
    {A B : SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (F : ∀ U : X.C, A.val.obj (op U) → B.val.obj (op U))
    (hadd : ∀ (U : X.C) (x y : A.val.obj (op U)), F U (x + y) = F U x + F U y)
    (hsmul : ∀ (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (x : A.val.obj (op U)),
      F U (r • x) = r • F U x)
    (hres : ∀ {U V : X.C} (g : V ⟶ U) (x : A.val.obj (op U)),
      F V (restrictSection X g x) = restrictSection X g (F U x))
    (U : X.C) (x : A.val.obj (op U)) :
    ((sheafHomOfSectionMaps X F hadd hsmul hres).val.app (op U)) x = F U x := rfl

end Sections

/-- Restriction of complexes of `O`-modules to a slice site commutes with the shift: in each
degree both complexes have the same objects, and the identity components form an isomorphism of
complexes. -/
noncomputable abbrev restrictComplexShiftIso
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (b : ℤ) :
    restrictComplex X (K⟦b⟧) U ≅ (restrictComplex X K U)⟦b⟧ :=
  (((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso b).app K

/-- `restrictComplexShiftIso` is the identity in each degree. -/
lemma restrictComplexShiftIso_hom_f
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (b p : ℤ) :
    (restrictComplexShiftIso X K U b).hom.f p = 𝟙 _ := rfl

/-- The inverse of `restrictComplexShiftIso` is the identity in each degree. -/
lemma restrictComplexShiftIso_inv_f
    (K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (b p : ℤ) :
    (restrictComplexShiftIso X K U b).inv.f p = 𝟙 _ := rfl

variable {K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

section CochainSourceShift

/-- The shift of the source of a cochain between restricted complexes: the degree-`n` cochains
from `K|_U` to `M|_U` are carried to the degree-`n'` cochains from `(K[b])|_U` to `M|_U`, where
`n + b = n'`. -/
noncomputable def cochainSourceShift (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    Cochain (restrictComplex X (K⟦b⟧) U) (restrictComplex X M U) n' :=
  (Cochain.ofHom (restrictComplexShiftIso X K U b).hom).comp
    (c.leftShift b n' hn') (zero_add n')

/-- The components of `cochainSourceShift`: the sign of the shift identification times the
evident reindexing. -/
lemma cochainSourceShift_v (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) (p q : ℤ)
    (hpq : p + n' = q) :
    (cochainSourceShift X U b n n' hn' c).v p q hpq =
      (b * n' + b * (b - 1) / 2).negOnePow • c.v (p + b) q (by omega) := by
  rw [cochainSourceShift, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.leftShift_v _ b n' hn' p q hpq (p + b) (by omega)]
  simp

/-- The shift of the source of a cochain is additive. -/
lemma cochainSourceShift_add (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c c' : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainSourceShift X U b n n' hn' (c + c') =
      cochainSourceShift X U b n n' hn' c + cochainSourceShift X U b n n' hn' c' := by
  rw [cochainSourceShift, cochainSourceShift, cochainSourceShift, Cochain.leftShift_add,
    Cochain.comp_add]

/-- The inverse of `cochainSourceShift`, unshifting the source of a cochain. -/
noncomputable def cochainSourceUnshift (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X (K⟦b⟧) U) (restrictComplex X M U) n') :
    Cochain (restrictComplex X K U) (restrictComplex X M U) n :=
  ((Cochain.ofHom (restrictComplexShiftIso X K U b).inv).comp c (zero_add n')).leftUnshift n hn'

/-- Unshifting the source undoes shifting it. -/
lemma cochainSourceUnshift_cochainSourceShift (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainSourceUnshift X U b n n' hn' (cochainSourceShift X U b n n' hn' c) = c := by
  rw [cochainSourceUnshift, cochainSourceShift, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, Iso.inv_hom_id, Cochain.id_comp, Cochain.leftUnshift_leftShift]

/-- Shifting the source undoes unshifting it. -/
lemma cochainSourceShift_cochainSourceUnshift (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X (K⟦b⟧) U) (restrictComplex X M U) n') :
    cochainSourceShift X U b n n' hn' (cochainSourceUnshift X U b n n' hn' c) = c := by
  rw [cochainSourceUnshift, cochainSourceShift, Cochain.leftShift_leftUnshift,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, Iso.hom_inv_id,
    Cochain.id_comp]

/-- The shift of the source of a cochain, as an additive equivalence. -/
noncomputable def cochainSourceShiftEquiv (U : X.C) (b n n' : ℤ) (hn' : n + b = n') :
    Cochain (restrictComplex X K U) (restrictComplex X M U) n ≃+
      Cochain (restrictComplex X (K⟦b⟧) U) (restrictComplex X M U) n' where
  toFun c := cochainSourceShift X U b n n' hn' c
  invFun c := cochainSourceUnshift X U b n n' hn' c
  left_inv c := cochainSourceUnshift_cochainSourceShift X U b n n' hn' c
  right_inv c := cochainSourceShift_cochainSourceUnshift X U b n n' hn' c
  map_add' c c' := cochainSourceShift_add X U b n n' hn' c c'

/-- `cochainSourceShiftEquiv` is `cochainSourceShift`. -/
@[simp]
lemma cochainSourceShiftEquiv_apply (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainSourceShiftEquiv X U b n n' hn' c = cochainSourceShift X U b n n' hn' c := rfl

/-- Shifting the source of a cochain multiplies the Hom-complex differential by the sign
`(-1)^b`, which is exactly the sign by which the differential of a shifted complex differs from
the original. -/
lemma cochainSourceShift_δ (U : X.C) (b n n' m m' : ℤ) (hn' : n + b = n') (hm' : m + b = m')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    δ n' m' (cochainSourceShift X U b n n' hn' c) =
      b.negOnePow • cochainSourceShift X U b m m' hm' (δ n m c) := by
  rw [cochainSourceShift, cochainSourceShift, δ_ofHom_comp,
    Cochain.δ_leftShift _ b n' m' hn' m hm', Cochain.comp_units_smul]

end CochainSourceShift

section SourceShift

/-- The map on sections underlying the source-shift identification of internal Hom
complexes. -/
noncomputable def sourceShiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U) :=
  ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n').symm
    (cochainSourceShift X U b n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s))

/-- The defining property of `sourceShiftFun`. -/
@[simp]
lemma sectionsEquiv_sourceShiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n' (sourceShiftFun X b n n' hn' U s) =
      cochainSourceShift X U b n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n').apply_symm_apply _

/-- The map on sections of the source shift is additive. -/
lemma sourceShiftFun_add (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s t : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    sourceShiftFun X b n n' hn' U (s + t) =
      sourceShiftFun X b n n' hn' U s + sourceShiftFun X b n n' hn' U t := by
  apply ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n').injective
  rw [map_add, sectionsEquiv_sourceShiftFun, sectionsEquiv_sourceShiftFun,
    sectionsEquiv_sourceShiftFun, map_add, cochainSourceShift_add]

/-- The map on sections of the source shift is linear over the sections of the structure
sheaf. -/
lemma sourceShiftFun_smul (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    sourceShiftFun X b n n' hn' U (r • s) = r • sourceShiftFun X b n n' hn' U s := by
  apply ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n').injective
  rw [sectionsEquiv_sourceShiftFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W g x => ?_
  rw [(sheafHomComplex X (K⟦b⟧) M).sectionsEquiv_smul U r n' p q hpq
      (sourceShiftFun X b n n' hn' U s) g x, sectionsEquiv_sourceShiftFun,
    cochainSourceShift_v, cochainSourceShift_v, unitsSmul_val_app_apply,
    unitsSmul_val_app_apply,
    (sheafHomComplex X K M).sectionsEquiv_smul U r n (p + b) q (by omega) s g x]
  exact smul_comm _ _ _

/-- The maps on sections of the source shift are compatible with restriction along arrows of
the site. -/
lemma sourceShiftFun_restrict (b n n' : ℤ) (hn' : n + b = n') {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    sourceShiftFun X b n n' hn' V (restrictSection X g s) =
      restrictSection X g (sourceShiftFun X b n n' hn' U s) := by
  apply ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv V n').injective
  rw [sectionsEquiv_sourceShiftFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W h x => ?_
  rw [cochainSourceShift_v, unitsSmul_val_app_apply,
    (sheafHomComplex X K M).sectionsEquiv_restrict g n (p + b) q (by omega) s h x,
    (sheafHomComplex X (K⟦b⟧) M).sectionsEquiv_restrict g n' p q hpq
      (sourceShiftFun X b n n' hn' U s) h x, sectionsEquiv_sourceShiftFun,
    cochainSourceShift_v]
  exact (unitsSmul_val_app_apply _
    (((sheafHomComplex X K M).sectionsEquiv U n s).v (p + b) q (by omega))
    (op (Over.mk (h ≫ g))) x).symm

/-- The source-shift identification of internal Hom complexes, in degree `n'`. -/
noncomputable def sourceShiftHom (b n n' : ℤ) (hn' : n + b = n') :
    (sheafHomComplex X K M).obj.X n ⟶ (sheafHomComplex X (K⟦b⟧) M).obj.X n' :=
  sheafHomOfSectionMaps X (sourceShiftFun X b n n' hn')
    (sourceShiftFun_add X b n n' hn') (sourceShiftFun_smul X b n n' hn')
    (fun g s => sourceShiftFun_restrict X b n n' hn' g s)

/-- `sourceShiftHom` acts on sections by shifting the source of a cochain. -/
@[simp]
lemma sectionsEquiv_sourceShiftHom (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n'
        ((sourceShiftHom X b n n' hn').val.app (op U) s) =
      cochainSourceShift X U b n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  sectionsEquiv_sourceShiftFun X b n n' hn' U s

/-- The map on sections underlying the inverse of the source-shift identification. -/
noncomputable def sourceUnshiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X K M).sectionsEquiv U n).symm
    (cochainSourceUnshift X U b n n' hn'
      ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n' s))

/-- The defining property of `sourceUnshiftFun`. -/
@[simp]
lemma sectionsEquiv_sourceUnshiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    (sheafHomComplex X K M).sectionsEquiv U n (sourceUnshiftFun X b n n' hn' U s) =
      cochainSourceUnshift X U b n n'
        hn' ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n' s) :=
  ((sheafHomComplex X K M).sectionsEquiv U n).apply_symm_apply _

/-- The two maps on sections of the source shift are mutually inverse. -/
lemma sourceUnshiftFun_sourceShiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    sourceUnshiftFun X b n n' hn' U (sourceShiftFun X b n n' hn' U s) = s := by
  apply ((sheafHomComplex X K M).sectionsEquiv U n).injective
  rw [sectionsEquiv_sourceUnshiftFun, sectionsEquiv_sourceShiftFun,
    cochainSourceUnshift_cochainSourceShift]

/-- The two maps on sections of the source shift are mutually inverse. -/
lemma sourceShiftFun_sourceUnshiftFun (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    sourceShiftFun X b n n' hn' U (sourceUnshiftFun X b n n' hn' U s) = s := by
  apply ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n').injective
  rw [sectionsEquiv_sourceShiftFun, sectionsEquiv_sourceUnshiftFun,
    cochainSourceShift_cochainSourceUnshift]

/-- The map on sections of the inverse source shift is additive. -/
lemma sourceUnshiftFun_add (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (s t : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    sourceUnshiftFun X b n n' hn' U (s + t) =
      sourceUnshiftFun X b n n' hn' U s + sourceUnshiftFun X b n n' hn' U t := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (sourceShiftFun_sourceUnshiftFun X b n n' hn' U) s
  obtain ⟨t, rfl⟩ :=
    Function.RightInverse.surjective (sourceShiftFun_sourceUnshiftFun X b n n' hn' U) t
  rw [← sourceShiftFun_add, sourceUnshiftFun_sourceShiftFun,
    sourceUnshiftFun_sourceShiftFun, sourceUnshiftFun_sourceShiftFun]

/-- The map on sections of the inverse source shift is linear over the sections of the
structure sheaf. -/
lemma sourceUnshiftFun_smul (b n n' : ℤ) (hn' : n + b = n') (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    sourceUnshiftFun X b n n' hn' U (r • s) = r • sourceUnshiftFun X b n n' hn' U s := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (sourceShiftFun_sourceUnshiftFun X b n n' hn' U) s
  rw [← sourceShiftFun_smul, sourceUnshiftFun_sourceShiftFun,
    sourceUnshiftFun_sourceShiftFun]

/-- The maps on sections of the inverse source shift are compatible with restriction along
arrows of the site. -/
lemma sourceUnshiftFun_restrict (b n n' : ℤ) (hn' : n + b = n') {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X (K⟦b⟧) M).obj.X n').val.obj (op U)) :
    sourceUnshiftFun X b n n' hn' V (restrictSection X g s) =
      restrictSection X g (sourceUnshiftFun X b n n' hn' U s) := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (sourceShiftFun_sourceUnshiftFun X b n n' hn' U) s
  rw [← sourceShiftFun_restrict, sourceUnshiftFun_sourceShiftFun,
    sourceUnshiftFun_sourceShiftFun]

/-- The inverse of the source-shift identification of internal Hom complexes, in degree
`n'`. -/
noncomputable def sourceUnshiftHom (b n n' : ℤ) (hn' : n + b = n') :
    (sheafHomComplex X (K⟦b⟧) M).obj.X n' ⟶ (sheafHomComplex X K M).obj.X n :=
  sheafHomOfSectionMaps X (sourceUnshiftFun X b n n' hn')
    (sourceUnshiftFun_add X b n n' hn') (sourceUnshiftFun_smul X b n n' hn')
    (fun g s => sourceUnshiftFun_restrict X b n n' hn' g s)

/-- The source-shift identification of internal Hom complexes, in degree `n'`, as an
isomorphism of sheaves of modules. -/
noncomputable def sourceShiftIsoX (b n n' : ℤ) (hn' : n + b = n') :
    (sheafHomComplex X K M).obj.X n ≅ (sheafHomComplex X (K⟦b⟧) M).obj.X n' where
  hom := sourceShiftHom X b n n' hn'
  inv := sourceUnshiftHom X b n n' hn'
  hom_inv_id := sheafHom_ext X fun U s =>
    sourceUnshiftFun_sourceShiftFun X b n n' hn' U s
  inv_hom_id := sheafHom_ext X fun U s =>
    sourceShiftFun_sourceUnshiftFun X b n n' hn' U s


/-- The differential of a shifted complex of sheaves of modules, on sections. -/
private lemma shiftObj_d_val_app_apply
    (H : CochainComplex (SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (b i j : ℤ) (U : X.C)
    (x : ((H⟦b⟧).X i).val.obj (op U)) :
    (((H⟦b⟧).d i j).val.app (op U)) x =
      b.negOnePow • ((H.d (i + b) (j + b)).val.app (op U) x) :=
  unitsSmul_val_app_apply _ _ _ x

/-- `sectionsEquiv` is compatible with multiplication by a unit integer. -/
private lemma sectionsEquiv_unitsSmul
    {L N : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (H : SheafHomComplex X L N) (U : X.C) (n : ℤ) (ε : ℤˣ)
    (s : (H.obj.X n).val.obj (op U)) :
    H.sectionsEquiv U n (ε • s) = ε • H.sectionsEquiv U n s :=
  map_zsmul _ (ε : ℤ) s

/-- Shifting the source of a cochain is compatible with multiplication by a unit integer. -/
private lemma cochainSourceShift_unitsSmul (U : X.C) (b n n' : ℤ) (hn' : n + b = n') (ε : ℤˣ)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainSourceShift X U b n n' hn' (ε • c) =
      ε • cochainSourceShift X U b n n' hn' c :=
  map_zsmul (cochainSourceShiftEquiv X U b n n' hn') (ε : ℤ) c

/-- The forward direction of `sourceShiftIsoX` is `sourceShiftHom`. -/
lemma sourceShiftIsoX_hom (b n n' : ℤ) (hn' : n + b = n') :
    (sourceShiftIsoX X (K := K) (M := M) b n n' hn').hom =
      sourceShiftHom X b n n' hn' := rfl

/-- The canonical identification `SheafHom(K, M)[-b] ≅ SheafHom(K[b], M)` of internal Hom
complexes on a ringed site: the source-shift half of the shift identification. -/
noncomputable def sheafHomSourceShiftIso (b : ℤ) :
    ((sheafHomComplex X K M).obj)⟦-b⟧ ≅ (sheafHomComplex X (K⟦b⟧) M).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => sourceShiftIsoX X b (n + -b) n (by omega))
    (fun i j _ => sheafHom_ext X fun U s => by
      apply ((sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U j).injective
      rw [comp_val_app_apply, comp_val_app_apply, sourceShiftIsoX_hom, sourceShiftIsoX_hom,
        (sheafHomComplex X (K⟦b⟧) M).sectionsEquiv_d U i j, sectionsEquiv_sourceShiftHom,
        sectionsEquiv_sourceShiftHom,
        cochainSourceShift_δ X U b (i + -b) i (j + -b) j (by omega) (by omega),
        shiftObj_d_val_app_apply, sectionsEquiv_unitsSmul, cochainSourceShift_unitsSmul,
        (sheafHomComplex X K M).sectionsEquiv_d U (i + -b) (j + -b), Int.negOnePow_neg])

/-- The degreewise components of `sheafHomSourceShiftIso`. -/
@[simp]
lemma sheafHomSourceShiftIso_hom_f (b n : ℤ) :
    (sheafHomSourceShiftIso X (K := K) (M := M) b).hom.f n =
      sourceShiftHom X b (n + -b) n (by omega) := rfl

/-- The source-shift identification acts on sections by shifting the source of a cochain. -/
lemma sectionsEquiv_sheafHomSourceShiftIso_hom (b n : ℤ) (U : X.C)
    (s : ((((sheafHomComplex X K M).obj)⟦-b⟧).X n).val.obj (op U)) :
    (sheafHomComplex X (K⟦b⟧) M).sectionsEquiv U n
        (((sheafHomSourceShiftIso X (K := K) (M := M) b).hom.f n).val.app (op U) s) =
      cochainSourceShift X U b (n + -b) n (by omega)
        ((sheafHomComplex X K M).sectionsEquiv U (n + -b) s) :=
  sectionsEquiv_sourceShiftHom X b (n + -b) n (by omega) U s

/-- The source-shift identification is natural in both complexes: it commutes with the maps
induced by `k : K' ⟶ K` and `g : M ⟶ M'`. -/
lemma sourceShiftHom_naturality (b n n' : ℤ) (hn' : n + b = n')
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    sourceShiftHom X (K := K) (M := M) b n n' hn' ≫
        homMapHom X ((CategoryTheory.shiftFunctor _ b).map k) g n' =
      homMapHom X k g n ≫ sourceShiftHom X (K := K') (M := M') b n n' hn' := by
  refine sheafHom_ext X fun U s => ?_
  apply ((sheafHomComplex X (K'⟦b⟧) M').sectionsEquiv U n').injective
  rw [comp_val_app_apply, comp_val_app_apply, sectionsEquiv_homMapHom,
    sectionsEquiv_sourceShiftHom, sectionsEquiv_sourceShiftHom, sectionsEquiv_homMapHom]
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, cochainSourceShift_v, cochainSourceShift_v, cochainConj_v,
    CochainComplex.shiftFunctor_map_f', Linear.units_smul_comp, Linear.comp_units_smul]

/-- `sheafHomSourceShiftIso` is natural in both complexes. -/
lemma sheafHomSourceShiftIso_hom_naturality (b : ℤ)
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    (sheafHomSourceShiftIso X (K := K) (M := M) b).hom ≫
        homMap X ((CategoryTheory.shiftFunctor _ b).map k) g =
      (CategoryTheory.shiftFunctor _ (-b)).map (homMap X k g) ≫
        (sheafHomSourceShiftIso X (K := K') (M := M') b).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simpa using sourceShiftHom_naturality X b (n + -b) n (by omega) k g

end SourceShift

section CochainTargetShift

/-- The shift of the target of a cochain between restricted complexes: the degree-`n` cochains
from `K|_U` to `M|_U` are carried to the degree-`n'` cochains from `K|_U` to `(M[a])|_U`, where
`n' + a = n`. -/
noncomputable def cochainTargetShift (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    Cochain (restrictComplex X K U) (restrictComplex X (M⟦a⟧) U) n' :=
  (c.rightShift a n' hn').comp
    (Cochain.ofHom (restrictComplexShiftIso X M U a).inv) (add_zero n')

/-- The components of `cochainTargetShift`: the evident reindexing, with no sign. -/
lemma cochainTargetShift_v (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) (p q : ℤ)
    (hpq : p + n' = q) :
    (cochainTargetShift X U a n n' hn' c).v p q hpq = c.v p (q + a) (by omega) := by
  rw [cochainTargetShift, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Cochain.rightShift_v _ a n' hn' p q hpq (q + a) (by omega)]
  simp

/-- The shift of the target of a cochain is additive. -/
lemma cochainTargetShift_add (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c c' : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainTargetShift X U a n n' hn' (c + c') =
      cochainTargetShift X U a n n' hn' c + cochainTargetShift X U a n n' hn' c' := by
  rw [cochainTargetShift, cochainTargetShift, cochainTargetShift, Cochain.rightShift_add,
    Cochain.add_comp]

/-- The inverse of `cochainTargetShift`, unshifting the target of a cochain. -/
noncomputable def cochainTargetUnshift (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X (M⟦a⟧) U) n') :
    Cochain (restrictComplex X K U) (restrictComplex X M U) n :=
  (c.comp (Cochain.ofHom (restrictComplexShiftIso X M U a).hom) (add_zero n')).rightUnshift n hn'

/-- Unshifting the target undoes shifting it. -/
lemma cochainTargetUnshift_cochainTargetShift (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainTargetUnshift X U a n n' hn' (cochainTargetShift X U a n n' hn' c) = c := by
  rw [cochainTargetUnshift, cochainTargetShift, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, Iso.inv_hom_id, Cochain.comp_id, Cochain.rightUnshift_rightShift]

/-- Shifting the target undoes unshifting it. -/
lemma cochainTargetShift_cochainTargetUnshift (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X (M⟦a⟧) U) n') :
    cochainTargetShift X U a n n' hn' (cochainTargetUnshift X U a n n' hn' c) = c := by
  rw [cochainTargetUnshift, cochainTargetShift, Cochain.rightShift_rightUnshift,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Iso.hom_inv_id,
    Cochain.comp_id]

/-- The shift of the target of a cochain, as an additive equivalence. -/
noncomputable def cochainTargetShiftEquiv (U : X.C) (a n n' : ℤ) (hn' : n' + a = n) :
    Cochain (restrictComplex X K U) (restrictComplex X M U) n ≃+
      Cochain (restrictComplex X K U) (restrictComplex X (M⟦a⟧) U) n' where
  toFun c := cochainTargetShift X U a n n' hn' c
  invFun c := cochainTargetUnshift X U a n n' hn' c
  left_inv c := cochainTargetUnshift_cochainTargetShift X U a n n' hn' c
  right_inv c := cochainTargetShift_cochainTargetUnshift X U a n n' hn' c
  map_add' c c' := cochainTargetShift_add X U a n n' hn' c c'

/-- `cochainTargetShiftEquiv` is `cochainTargetShift`. -/
@[simp]
lemma cochainTargetShiftEquiv_apply (U : X.C) (a n n' : ℤ) (hn' : n' + a = n)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainTargetShiftEquiv X U a n n' hn' c = cochainTargetShift X U a n n' hn' c := rfl

/-- Shifting the target of a cochain multiplies the Hom-complex differential by the sign
`(-1)^a`, which is exactly the sign by which the differential of a shifted complex differs from
the original. -/
lemma cochainTargetShift_δ (U : X.C) (a n n' m m' : ℤ) (hn' : n' + a = n) (hm' : m' + a = m)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    δ n' m' (cochainTargetShift X U a n n' hn' c) =
      a.negOnePow • cochainTargetShift X U a m m' hm' (δ n m c) := by
  rw [cochainTargetShift, cochainTargetShift, δ_comp_ofHom,
    Cochain.δ_rightShift _ a n' m' hn' m hm', Cochain.units_smul_comp]

/-- Shifting the target of a cochain is compatible with multiplication by a unit integer. -/
private lemma cochainTargetShift_unitsSmul (U : X.C) (a n n' : ℤ) (hn' : n' + a = n) (ε : ℤˣ)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainTargetShift X U a n n' hn' (ε • c) =
      ε • cochainTargetShift X U a n n' hn' c :=
  map_zsmul (cochainTargetShiftEquiv X U a n n' hn') (ε : ℤ) c

end CochainTargetShift

section TargetShift

/-- The map on sections underlying the target-shift identification of internal Hom
complexes. -/
noncomputable def targetShiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U) :=
  ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n').symm
    (cochainTargetShift X U a n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s))

/-- The defining property of `targetShiftFun`. -/
@[simp]
lemma sectionsEquiv_targetShiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n' (targetShiftFun X a n n' hn' U s) =
      cochainTargetShift X U a n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n').apply_symm_apply _

/-- The map on sections of the target shift is additive. -/
lemma targetShiftFun_add (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s t : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    targetShiftFun X a n n' hn' U (s + t) =
      targetShiftFun X a n n' hn' U s + targetShiftFun X a n n' hn' U t := by
  apply ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n').injective
  rw [map_add, sectionsEquiv_targetShiftFun, sectionsEquiv_targetShiftFun,
    sectionsEquiv_targetShiftFun, map_add, cochainTargetShift_add]

/-- The map on sections of the target shift is linear over the sections of the structure
sheaf. -/
lemma targetShiftFun_smul (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    targetShiftFun X a n n' hn' U (r • s) = r • targetShiftFun X a n n' hn' U s := by
  apply ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n').injective
  rw [sectionsEquiv_targetShiftFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W g x => ?_
  rw [(sheafHomComplex X K (M⟦a⟧)).sectionsEquiv_smul U r n' p q hpq
      (targetShiftFun X a n n' hn' U s) g x, sectionsEquiv_targetShiftFun,
    cochainTargetShift_v, cochainTargetShift_v,
    (sheafHomComplex X K M).sectionsEquiv_smul U r n p (q + a) (by omega) s g x]

/-- The maps on sections of the target shift are compatible with restriction along arrows of
the site. -/
lemma targetShiftFun_restrict (a n n' : ℤ) (hn' : n' + a = n) {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    targetShiftFun X a n n' hn' V (restrictSection X g s) =
      restrictSection X g (targetShiftFun X a n n' hn' U s) := by
  apply ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv V n').injective
  rw [sectionsEquiv_targetShiftFun]
  refine Cochain.ext _ _ fun p q hpq => over_hom_ext X fun W h x => ?_
  rw [cochainTargetShift_v,
    (sheafHomComplex X K M).sectionsEquiv_restrict g n p (q + a) (by omega) s h x,
    (sheafHomComplex X K (M⟦a⟧)).sectionsEquiv_restrict g n' p q hpq
      (targetShiftFun X a n n' hn' U s) h x, sectionsEquiv_targetShiftFun,
    cochainTargetShift_v]

/-- The target-shift identification of internal Hom complexes, in degree `n'`. -/
noncomputable def targetShiftHom (a n n' : ℤ) (hn' : n' + a = n) :
    (sheafHomComplex X K M).obj.X n ⟶ (sheafHomComplex X K (M⟦a⟧)).obj.X n' :=
  sheafHomOfSectionMaps X (targetShiftFun X a n n' hn')
    (targetShiftFun_add X a n n' hn') (targetShiftFun_smul X a n n' hn')
    (fun g s => targetShiftFun_restrict X a n n' hn' g s)

/-- `targetShiftHom` acts on sections by shifting the target of a cochain. -/
@[simp]
lemma sectionsEquiv_targetShiftHom (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    (sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n'
        ((targetShiftHom X a n n' hn').val.app (op U) s) =
      cochainTargetShift X U a n n' hn' ((sheafHomComplex X K M).sectionsEquiv U n s) :=
  sectionsEquiv_targetShiftFun X a n n' hn' U s

/-- The map on sections underlying the inverse of the target-shift identification. -/
noncomputable def targetUnshiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    ((sheafHomComplex X K M).obj.X n).val.obj (op U) :=
  ((sheafHomComplex X K M).sectionsEquiv U n).symm
    (cochainTargetUnshift X U a n n' hn'
      ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n' s))

/-- The defining property of `targetUnshiftFun`. -/
@[simp]
lemma sectionsEquiv_targetUnshiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    (sheafHomComplex X K M).sectionsEquiv U n (targetUnshiftFun X a n n' hn' U s) =
      cochainTargetUnshift X U a n n'
        hn' ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n' s) :=
  ((sheafHomComplex X K M).sectionsEquiv U n).apply_symm_apply _

/-- The two maps on sections of the target shift are mutually inverse. -/
lemma targetUnshiftFun_targetShiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) :
    targetUnshiftFun X a n n' hn' U (targetShiftFun X a n n' hn' U s) = s := by
  apply ((sheafHomComplex X K M).sectionsEquiv U n).injective
  rw [sectionsEquiv_targetUnshiftFun, sectionsEquiv_targetShiftFun,
    cochainTargetUnshift_cochainTargetShift]

/-- The two maps on sections of the target shift are mutually inverse. -/
lemma targetShiftFun_targetUnshiftFun (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    targetShiftFun X a n n' hn' U (targetUnshiftFun X a n n' hn' U s) = s := by
  apply ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n').injective
  rw [sectionsEquiv_targetShiftFun, sectionsEquiv_targetUnshiftFun,
    cochainTargetShift_cochainTargetUnshift]

/-- The map on sections of the inverse target shift is additive. -/
lemma targetUnshiftFun_add (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (s t : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    targetUnshiftFun X a n n' hn' U (s + t) =
      targetUnshiftFun X a n n' hn' U s + targetUnshiftFun X a n n' hn' U t := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (targetShiftFun_targetUnshiftFun X a n n' hn' U) s
  obtain ⟨t, rfl⟩ :=
    Function.RightInverse.surjective (targetShiftFun_targetUnshiftFun X a n n' hn' U) t
  rw [← targetShiftFun_add, targetUnshiftFun_targetShiftFun,
    targetUnshiftFun_targetShiftFun, targetUnshiftFun_targetShiftFun]

/-- The map on sections of the inverse target shift is linear over the sections of the
structure sheaf. -/
lemma targetUnshiftFun_smul (a n n' : ℤ) (hn' : n' + a = n) (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    targetUnshiftFun X a n n' hn' U (r • s) = r • targetUnshiftFun X a n n' hn' U s := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (targetShiftFun_targetUnshiftFun X a n n' hn' U) s
  rw [← targetShiftFun_smul, targetUnshiftFun_targetShiftFun,
    targetUnshiftFun_targetShiftFun]

/-- The maps on sections of the inverse target shift are compatible with restriction along
arrows of the site. -/
lemma targetUnshiftFun_restrict (a n n' : ℤ) (hn' : n' + a = n) {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X K (M⟦a⟧)).obj.X n').val.obj (op U)) :
    targetUnshiftFun X a n n' hn' V (restrictSection X g s) =
      restrictSection X g (targetUnshiftFun X a n n' hn' U s) := by
  obtain ⟨s, rfl⟩ :=
    Function.RightInverse.surjective (targetShiftFun_targetUnshiftFun X a n n' hn' U) s
  rw [← targetShiftFun_restrict, targetUnshiftFun_targetShiftFun,
    targetUnshiftFun_targetShiftFun]

/-- The inverse of the target-shift identification of internal Hom complexes, in degree
`n'`. -/
noncomputable def targetUnshiftHom (a n n' : ℤ) (hn' : n' + a = n) :
    (sheafHomComplex X K (M⟦a⟧)).obj.X n' ⟶ (sheafHomComplex X K M).obj.X n :=
  sheafHomOfSectionMaps X (targetUnshiftFun X a n n' hn')
    (targetUnshiftFun_add X a n n' hn') (targetUnshiftFun_smul X a n n' hn')
    (fun g s => targetUnshiftFun_restrict X a n n' hn' g s)

/-- The target-shift identification of internal Hom complexes, in degree `n'`, as an
isomorphism of sheaves of modules. -/
noncomputable def targetShiftIsoX (a n n' : ℤ) (hn' : n' + a = n) :
    (sheafHomComplex X K M).obj.X n ≅ (sheafHomComplex X K (M⟦a⟧)).obj.X n' where
  hom := targetShiftHom X a n n' hn'
  inv := targetUnshiftHom X a n n' hn'
  hom_inv_id := sheafHom_ext X fun U s =>
    targetUnshiftFun_targetShiftFun X a n n' hn' U s
  inv_hom_id := sheafHom_ext X fun U s =>
    targetShiftFun_targetUnshiftFun X a n n' hn' U s

/-- The forward direction of `targetShiftIsoX` is `targetShiftHom`. -/
lemma targetShiftIsoX_hom (a n n' : ℤ) (hn' : n' + a = n) :
    (targetShiftIsoX X (K := K) (M := M) a n n' hn').hom =
      targetShiftHom X a n n' hn' := rfl

/-- The canonical identification `SheafHom(K, M)[a] ≅ SheafHom(K, M[a])` of internal Hom
complexes on a ringed site: the target-shift half of the shift identification. -/
noncomputable def sheafHomTargetShiftIso (a : ℤ) :
    ((sheafHomComplex X K M).obj)⟦a⟧ ≅ (sheafHomComplex X K (M⟦a⟧)).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => targetShiftIsoX X a (n + a) n (by omega))
    (fun i j _ => sheafHom_ext X fun U s => by
      apply ((sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U j).injective
      rw [comp_val_app_apply, comp_val_app_apply, targetShiftIsoX_hom, targetShiftIsoX_hom,
        (sheafHomComplex X K (M⟦a⟧)).sectionsEquiv_d U i j, sectionsEquiv_targetShiftHom,
        sectionsEquiv_targetShiftHom,
        cochainTargetShift_δ X U a (i + a) i (j + a) j (by omega) (by omega),
        shiftObj_d_val_app_apply, sectionsEquiv_unitsSmul, cochainTargetShift_unitsSmul,
        (sheafHomComplex X K M).sectionsEquiv_d U (i + a) (j + a)])

/-- The degreewise components of `sheafHomTargetShiftIso`. -/
@[simp]
lemma sheafHomTargetShiftIso_hom_f (a n : ℤ) :
    (sheafHomTargetShiftIso X (K := K) (M := M) a).hom.f n =
      targetShiftHom X a (n + a) n (by omega) := rfl

/-- The target-shift identification acts on sections by shifting the target of a cochain. -/
lemma sectionsEquiv_sheafHomTargetShiftIso_hom (a n : ℤ) (U : X.C)
    (s : ((((sheafHomComplex X K M).obj)⟦a⟧).X n).val.obj (op U)) :
    (sheafHomComplex X K (M⟦a⟧)).sectionsEquiv U n
        (((sheafHomTargetShiftIso X (K := K) (M := M) a).hom.f n).val.app (op U) s) =
      cochainTargetShift X U a (n + a) n (by omega)
        ((sheafHomComplex X K M).sectionsEquiv U (n + a) s) :=
  sectionsEquiv_targetShiftHom X a (n + a) n (by omega) U s

/-- The target-shift identification is natural in both complexes: it commutes with the maps
induced by `k : K' ⟶ K` and `g : M ⟶ M'`. -/
lemma targetShiftHom_naturality (a n n' : ℤ) (hn' : n' + a = n)
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    targetShiftHom X (K := K) (M := M) a n n' hn' ≫
        homMapHom X k ((CategoryTheory.shiftFunctor _ a).map g) n' =
      homMapHom X k g n ≫ targetShiftHom X (K := K') (M := M') a n n' hn' := by
  refine sheafHom_ext X fun U s => ?_
  apply ((sheafHomComplex X K' (M'⟦a⟧)).sectionsEquiv U n').injective
  rw [comp_val_app_apply, comp_val_app_apply, sectionsEquiv_homMapHom,
    sectionsEquiv_targetShiftHom, sectionsEquiv_targetShiftHom, sectionsEquiv_homMapHom]
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, cochainTargetShift_v, cochainTargetShift_v, cochainConj_v,
    CochainComplex.shiftFunctor_map_f']

/-- `sheafHomTargetShiftIso` is natural in both complexes. -/
lemma sheafHomTargetShiftIso_hom_naturality (a : ℤ)
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    (sheafHomTargetShiftIso X (K := K) (M := M) a).hom ≫
        homMap X k ((CategoryTheory.shiftFunctor _ a).map g) =
      (CategoryTheory.shiftFunctor _ a).map (homMap X k g) ≫
        (sheafHomTargetShiftIso X (K := K') (M := M') a).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simpa using targetShiftHom_naturality X a (n + a) n (by omega) k g

end TargetShift

section BothShifts

/-- The two-sided shift identification of internal Hom complexes, in a single degree: shift the
source, then the target. -/
noncomputable def shiftIsoX (a b n n' : ℤ) (hn' : n' + a = n + b) :
    (sheafHomComplex X K M).obj.X n ≅ (sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).obj.X n' :=
  sourceShiftIsoX X b n (n + b) rfl ≪≫ targetShiftIsoX X a (n + b) n' hn'

/-- The forward direction of `shiftIsoX` is the source shift followed by the target shift. -/
lemma shiftIsoX_hom (a b n n' : ℤ) (hn' : n' + a = n + b) :
    (shiftIsoX X (K := K) (M := M) a b n n' hn').hom =
      sourceShiftHom X b n (n + b) rfl ≫ targetShiftHom X a (n + b) n' hn' := rfl

/-- The two-sided shift identification acts on sections over `U` in degree `n'` by the sign
`(-1)^(b (n + b) + b (b - 1) / 2)` times the evident reindexing of homogeneous components. -/
lemma sectionsEquiv_shiftIsoX_hom_v (a b n n' : ℤ) (hn' : n' + a = n + b) (U : X.C)
    (s : ((sheafHomComplex X K M).obj.X n).val.obj (op U)) (p q : ℤ) (hpq : p + n' = q) :
    (((sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).sectionsEquiv U n'
          (((shiftIsoX X a b n n' hn').hom).val.app (op U) s)).v p q hpq) =
      (b * (n + b) + b * (b - 1) / 2).negOnePow •
        (((sheafHomComplex X K M).sectionsEquiv U n s).v (p + b) (q + a) (by omega)) := by
  rw [shiftIsoX_hom, comp_val_app_apply, sectionsEquiv_targetShiftHom, cochainTargetShift_v,
    sectionsEquiv_sourceShiftHom, cochainSourceShift_v]

/-- The canonical identification `SheafHom(K, M)[a - b] ≅ SheafHom(K[b], M[a])` of internal Hom
complexes on a ringed site: the sheaf-theoretic analogue of the shift identification of Hom
complexes of modules over a ring. -/
noncomputable def sheafHomShiftIso (a b : ℤ) :
    ((sheafHomComplex X K M).obj)⟦a - b⟧ ≅ (sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => shiftIsoX X a b (n + (a - b)) n (by omega))
    (fun i j _ => sheafHom_ext X fun U s => by
      apply ((sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).sectionsEquiv U j).injective
      rw [comp_val_app_apply, comp_val_app_apply, shiftIsoX_hom, shiftIsoX_hom,
        comp_val_app_apply, comp_val_app_apply,
        (sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).sectionsEquiv_d U i j,
        sectionsEquiv_targetShiftHom, sectionsEquiv_targetShiftHom,
        cochainTargetShift_δ X U a (i + (a - b) + b) i (j + (a - b) + b) j
          (by omega) (by omega),
        sectionsEquiv_sourceShiftHom, sectionsEquiv_sourceShiftHom,
        cochainSourceShift_δ X U b (i + (a - b)) (i + (a - b) + b) (j + (a - b))
          (j + (a - b) + b) rfl rfl,
        cochainTargetShift_unitsSmul, shiftObj_d_val_app_apply, sectionsEquiv_unitsSmul,
        cochainSourceShift_unitsSmul, cochainTargetShift_unitsSmul,
        (sheafHomComplex X K M).sectionsEquiv_d U (i + (a - b)) (j + (a - b)),
        Int.negOnePow_sub, smul_smul])

/-- The degreewise components of `sheafHomShiftIso`. -/
@[simp]
lemma sheafHomShiftIso_hom_f (a b n : ℤ) :
    (sheafHomShiftIso X (K := K) (M := M) a b).hom.f n =
      (shiftIsoX X a b (n + (a - b)) n (by omega)).hom := rfl

/-- The two-sided shift identification acts on sections over `U` in degree `n` by the sign
`(-1)^(b (n + a) + b (b - 1) / 2)` times the evident reindexing of homogeneous components. -/
lemma sectionsEquiv_sheafHomShiftIso_hom_v (a b n : ℤ) (U : X.C)
    (s : ((((sheafHomComplex X K M).obj)⟦a - b⟧).X n).val.obj (op U)) (p q : ℤ)
    (hpq : p + n = q) :
    (((sheafHomComplex X (K⟦b⟧) (M⟦a⟧)).sectionsEquiv U n
          (((sheafHomShiftIso X a b).hom.f n).val.app (op U) s)).v p q hpq) =
      (b * (n + (a - b) + b) + b * (b - 1) / 2).negOnePow •
        (((sheafHomComplex X K M).sectionsEquiv U (n + (a - b)) s).v (p + b) (q + a)
          (by omega)) :=
  sectionsEquiv_shiftIsoX_hom_v X a b (n + (a - b)) n (by omega) U s p q hpq

/-- The two-sided shift identification is natural in both complexes. -/
lemma shiftIsoX_hom_naturality (a b n n' : ℤ) (hn' : n' + a = n + b)
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    (shiftIsoX X (K := K) (M := M) a b n n' hn').hom ≫
        homMapHom X ((CategoryTheory.shiftFunctor _ b).map k)
          ((CategoryTheory.shiftFunctor _ a).map g) n' =
      homMapHom X k g n ≫ (shiftIsoX X (K := K') (M := M') a b n n' hn').hom := by
  rw [shiftIsoX_hom, shiftIsoX_hom, Category.assoc, targetShiftHom_naturality,
    ← Category.assoc, sourceShiftHom_naturality, Category.assoc]

/-- `sheafHomShiftIso` is natural in both complexes. -/
lemma sheafHomShiftIso_hom_naturality (a b : ℤ)
    {K' M' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    (sheafHomShiftIso X (K := K) (M := M) a b).hom ≫
        homMap X ((CategoryTheory.shiftFunctor _ b).map k)
          ((CategoryTheory.shiftFunctor _ a).map g) =
      (CategoryTheory.shiftFunctor _ (a - b)).map (homMap X k g) ≫
        (sheafHomShiftIso X (K := K') (M := M') a b).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simpa using shiftIsoX_hom_naturality X a b (n + (a - b)) n (by omega) k g

end BothShifts

end AlgebraicGeometry.RingedSite

end
