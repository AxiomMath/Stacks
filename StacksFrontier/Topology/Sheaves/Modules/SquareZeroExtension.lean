module

public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksFrontier.AlgebraicGeometry.Smooth.SqZeroAlgebra
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The square-zero extension of a sheaf of commutative rings by a sheaf of modules

For a sheaf of commutative rings `O` on a topological space `Z` and a sheaf of `O`-modules `N`,
the sections of `O` and of `N` over an open `V` assemble into the trivial square-zero extension
`O(V) ⋉ N(V)`, and these form a sheaf of commutative rings on `Z`, written `O ⋉ N` below.

The point of the construction is that a relative derivation of `O` with values in `N` is the same
thing as a section of the projection `O ⋉ N ⟶ O` which is trivial on the base: the Leibniz rule
is exactly multiplicativity of `a ↦ (a, d a)`. Combined with an adjunction, this turns a statement
about derivations into a statement about morphisms of sheaves of rings, which is how
`AlgebraicGeometry.SheafOfModules.isInverseImageDerivationComparison` is proved.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.sqZeroPresheaf`: the presheaf of commutative rings
  `V ↦ O(V) ⋉ N(V)`.
* `AlgebraicGeometry.SheafOfModules.sqZeroSheaf`: the same as a sheaf of commutative rings.
* `AlgebraicGeometry.SheafOfModules.sqZeroProj`: the projection `O ⋉ N ⟶ O`.
* `AlgebraicGeometry.SheafOfModules.sqZeroInl`: the zero section `O ⟶ O ⋉ N`.
* `AlgebraicGeometry.SheafOfModules.sectionRestrict`: the restriction maps of `N`, as additive
  maps between the plain section groups.

## Main results

* `AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_isSheaf`: the square-zero extension is a
  sheaf, because a section of it is a pair of sections and restriction acts componentwise.

## Implementation notes

The pure-algebra half of the construction — the square-zero extension of one commutative ring by
one module, a map satisfying the Leibniz rule read as a ring homomorphism into it, and its
functoriality — is `Stacks.Smooth.sqZeroRingHom` and `Stacks.Smooth.sqZeroMap` of
`StacksFrontier.AlgebraicGeometry.Smooth.SqZeroAlgebra`, which this file imports rather than
repeating. The construction here is the general one: the square-zero extension of the structure
sheaf of a scheme, `Stacks.Smooth.sqZeroSheaf`, is this one at `O := X.sheaf` and is defined as
such.

Two instances are supplied that Mathlib's do not cover. Mathlib has
`Module (R.obj X) (M.obj X)` for `M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)`, but
here the ring presheaf arrives as `(underlyingRingSheaf O).obj`, which is only *definitionally*
`O.obj ⋙ forget₂ _ _`, so instance search cannot see it; `sqZeroPresheaf` needs the module
structure over the commutative ring of sections to form the square-zero extension at all. They
are `scoped` to `AlgebraicGeometry.SheafOfModules` so that they are active exactly where that
spelling is used. `Stacks.Smooth.moduleMulOpposite`, the action of the opposite ring that
`TrivSqZeroExt.commRing` asks for, is a local instance of its own file and has to be re-enabled
here.

The second components of sections are carried in two definitionally equal spellings,
`N.val.obj V` and `N.val.presheaf.obj V`. Restriction is packaged as `sectionRestrict` in the
first spelling, which is the one the derivations use, while the sheaf condition has to be stated
in the second, which is the one carrying a genuine functor and hence Mathlib's gluing lemma. Both
forms of the component lemma for restriction are therefore provided.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace
open CategoryTheory.Functor
open Stacks.Smooth

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {Z : TopCat.{u}} {O : TopCat.Sheaf CommRingCat.{u} Z}
    {N : _root_.SheafOfModules.{u} (underlyingRingSheaf O)}

/-- The sections of a sheaf of modules over `O` form a module over the commutative ring of
sections of `O`. Mathlib's instance is stated for a presheaf of modules over `R ⋙ forget₂ _ _`,
which `(underlyingRingSheaf O).obj` only matches up to unfolding, so instance search misses
it. -/
scoped instance moduleSections (V : (Opens Z)ᵒᵖ) : Module ↥(O.obj.obj V) ↥(N.val.obj V) :=
  (N.val.obj V).isModule

/-- `AlgebraicGeometry.SheafOfModules.moduleSections` at the other spelling of the sections of a
sheaf of modules, the one used by its underlying presheaf of abelian groups. -/
scoped instance modulePresheafSections (V : (Opens Z)ᵒᵖ) :
    Module ↥(O.obj.obj V) ↥(N.val.presheaf.obj V) :=
  (N.val.obj V).isModule

variable (N) in
/-- Restriction of sections of a sheaf of modules, as an additive map between the plain section
groups. -/
noncomputable def sectionRestrict {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V') :
    ↥(N.val.obj V) →+ ↥(N.val.obj V') :=
  (N.val.presheaf.map h).hom

/-- `sectionRestrict` is the restriction map of `N`. -/
theorem sectionRestrict_apply {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V') (m : ↥(N.val.obj V)) :
    sectionRestrict N h m = N.val.map h m :=
  rfl

/-- `sectionRestrict` is the restriction map of the underlying presheaf of abelian groups of
`N`. -/
theorem sectionRestrict_eq_presheaf_map {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (m : ↥(N.val.obj V)) :
    sectionRestrict N h m = (N.val.presheaf.map h).hom m :=
  rfl

/-- Restriction along the identity is the identity. -/
theorem sectionRestrict_id_apply (V : (Opens Z)ᵒᵖ) (m : ↥(N.val.obj V)) :
    sectionRestrict N (𝟙 V) m = m := by
  change (N.val.presheaf.map (𝟙 V)).hom m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Restriction along a composite is the composite of the restrictions. -/
theorem sectionRestrict_comp_apply {V V' V'' : (Opens Z)ᵒᵖ} (h : V ⟶ V') (h' : V' ⟶ V'')
    (m : ↥(N.val.obj V)) :
    sectionRestrict N (h ≫ h') m = sectionRestrict N h' (sectionRestrict N h m) := by
  change (N.val.presheaf.map (h ≫ h')).hom m = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- Restriction of sections is semilinear over the restriction map of `O`. -/
theorem sectionRestrict_smul {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (r : ↥(O.obj.obj V)) (m : ↥(N.val.obj V)) :
    sectionRestrict N h (r • m) = (O.obj.map h).hom r • sectionRestrict N h m :=
  N.val.map_smul h r m

variable (O N)

/-- The presheaf of commutative rings whose sections over an open `V` are the trivial square-zero
extension of `O(V)` by `N(V)`. -/
noncomputable def sqZeroPresheaf : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u} where
  obj V := CommRingCat.of (TrivSqZeroExt ↥(O.obj.obj V) ↥(N.val.obj V))
  map h := CommRingCat.ofHom (sqZeroMap (O.obj.map h).hom
    (sectionRestrict N h) (sectionRestrict_smul h))
  map_id V := CommRingCat.hom_ext (RingHom.ext fun x ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · refine (sqZeroMap_fst _ _ (sectionRestrict_smul (N := N) (𝟙 V)) x).trans ?_
      simp
    · exact (sqZeroMap_snd _ _ (sectionRestrict_smul (N := N) (𝟙 V)) x).trans
        (sectionRestrict_id_apply V (TrivSqZeroExt.snd x)))
  map_comp h h' := CommRingCat.hom_ext (RingHom.ext fun x ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · refine (sqZeroMap_fst _ _ (sectionRestrict_smul (N := N) (h ≫ h')) x).trans ?_
      refine Eq.trans ?_ (sqZeroMap_fst _ _ (sectionRestrict_smul (N := N) h') _).symm
      refine Eq.trans ?_ (congrArg (O.obj.map h').hom
        (sqZeroMap_fst _ _ (sectionRestrict_smul (N := N) h) x).symm)
      simp
    · refine (sqZeroMap_snd _ _ (sectionRestrict_smul (N := N) (h ≫ h')) x).trans ?_
      refine Eq.trans ?_ (sqZeroMap_snd _ _ (sectionRestrict_smul (N := N) h') _).symm
      refine Eq.trans ?_ (congrArg (sectionRestrict N h')
        (sqZeroMap_snd _ _ (sectionRestrict_smul (N := N) h) x).symm)
      exact sectionRestrict_comp_apply h h' (TrivSqZeroExt.snd x))

/-- The first component of a restriction in the square-zero extension. -/
@[simp]
theorem sqZeroPresheaf_map_fst {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (x : (sqZeroPresheaf O N).obj V) :
    (((sqZeroPresheaf O N).map h).hom x).fst = (O.obj.map h).hom x.fst :=
  sqZeroMap_fst _ _ (sectionRestrict_smul h) x

/-- The second component of a restriction in the square-zero extension. -/
@[simp]
theorem sqZeroPresheaf_map_snd {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (x : (sqZeroPresheaf O N).obj V) :
    (((sqZeroPresheaf O N).map h).hom x).snd = sectionRestrict N h x.snd :=
  sqZeroMap_snd _ _ (sectionRestrict_smul h) x

/-- The second component of a restriction in the square-zero extension, in the spelling used by
the underlying presheaf of abelian groups of `N`. -/
theorem sqZeroPresheaf_map_snd_presheaf {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (x : (sqZeroPresheaf O N).obj V) :
    (((sqZeroPresheaf O N).map h).hom x).snd = (N.val.presheaf.map h).hom x.snd :=
  sqZeroMap_snd _ _ (sectionRestrict_smul h) x

/-- **The square-zero extension of a sheaf of commutative rings by a sheaf of modules is a
sheaf.** A section of it is a pair of a section of `O` and a section of `N`, and restriction acts
componentwise, so a compatible family glues componentwise and uniquely. -/
theorem sqZeroPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (sqZeroPresheaf O N) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hfst : TopCat.Presheaf.IsCompatible O.obj U (fun i ↦ (sf i).fst) := fun i j ↦ by
    have h := congrArg TrivSqZeroExt.fst (hsf i j)
    rwa [sqZeroPresheaf_map_fst, sqZeroPresheaf_map_fst] at h
  have hsnd : TopCat.Presheaf.IsCompatible N.val.presheaf U (fun i ↦ (sf i).snd) := fun i j ↦ by
    have h := congrArg TrivSqZeroExt.snd (hsf i j)
    rwa [sqZeroPresheaf_map_snd_presheaf, sqZeroPresheaf_map_snd_presheaf] at h
  have hO : TopCat.Presheaf.IsSheaf O.obj := O.property
  have hN : TopCat.Presheaf.IsSheaf N.val.presheaf := N.isSheaf
  obtain ⟨r, hr, hruniq⟩ := hO.isSheafUniqueGluing U _ hfst
  obtain ⟨m, hm, hmuniq⟩ := hN.isSheafUniqueGluing U _ hsnd
  refine ⟨TrivSqZeroExt.inl r + TrivSqZeroExt.inr m, fun i ↦ TrivSqZeroExt.ext ?_ ?_,
    fun s hs ↦ TrivSqZeroExt.ext ?_ ?_⟩
  · rw [sqZeroPresheaf_map_fst]
    exact (congrArg _ (fst_inl_add_inr r m)).trans (hr i)
  · rw [sqZeroPresheaf_map_snd_presheaf]
    exact (congrArg _ (snd_inl_add_inr r m)).trans (hm i)
  · refine (hruniq _ fun i ↦ ?_).trans (fst_inl_add_inr r m).symm
    rw [← sqZeroPresheaf_map_fst]
    exact congrArg TrivSqZeroExt.fst (hs i)
  · refine (hmuniq _ fun i ↦ ?_).trans (snd_inl_add_inr r m).symm
    rw [← sqZeroPresheaf_map_snd_presheaf]
    exact congrArg TrivSqZeroExt.snd (hs i)

/-- The square-zero extension of a sheaf of commutative rings `O` by a sheaf of `O`-modules `N`,
as a sheaf of commutative rings. -/
noncomputable def sqZeroSheaf : TopCat.Sheaf CommRingCat.{u} Z :=
  ⟨sqZeroPresheaf O N, sqZeroPresheaf_isSheaf O N⟩

/-- The underlying presheaf of `sqZeroSheaf O N` is `sqZeroPresheaf O N`. -/
theorem sqZeroSheaf_obj : (sqZeroSheaf O N).obj = sqZeroPresheaf O N :=
  rfl

/-- The projection from the square-zero extension to the base, as a morphism of sheaves of
commutative rings. -/
noncomputable def sqZeroProj : sqZeroSheaf O N ⟶ O :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom
        (TrivSqZeroExt.fstHom ↥(O.obj.obj V) ↥(O.obj.obj V) ↥(N.val.obj V)).toRingHom
      naturality := fun _ _ h ↦ CommRingCat.hom_ext (RingHom.ext fun x ↦
        sqZeroPresheaf_map_fst O N h x) }

/-- The projection `sqZeroProj` takes a section to its first component. -/
@[simp]
theorem sqZeroProj_app_apply (V : (Opens Z)ᵒᵖ) (x : (sqZeroSheaf O N).obj.obj V) :
    ((sqZeroProj O N).hom.app V).hom x = x.fst :=
  rfl

/-- The zero section of the square-zero extension, as a morphism of sheaves of commutative
rings. -/
noncomputable def sqZeroInl : O ⟶ sqZeroSheaf O N :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom (TrivSqZeroExt.inlHom ↥(O.obj.obj V) ↥(N.val.obj V))
      naturality := fun V _ h ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦ by
        have e1 := sqZeroPresheaf_map_fst O N h (TrivSqZeroExt.inl (M := ↥(N.val.obj V)) a)
        have e2 := sqZeroPresheaf_map_snd O N h (TrivSqZeroExt.inl (M := ↥(N.val.obj V)) a)
        change TrivSqZeroExt.inl ((O.obj.map h).hom a)
            = ((sqZeroPresheaf O N).map h).hom (TrivSqZeroExt.inl a)
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [e1]; simp
        · rw [e2]; simp) }

/-- The first component of the zero section `sqZeroInl` at `a` is `a`. -/
@[simp]
theorem sqZeroInl_app_apply_fst (V : (Opens Z)ᵒᵖ) (a : ↥(O.obj.obj V)) :
    (((sqZeroInl O N).hom.app V).hom a).fst = a :=
  TrivSqZeroExt.fst_inl _ _

/-- The second component of the zero section `sqZeroInl` is zero. -/
@[simp]
theorem sqZeroInl_app_apply_snd (V : (Opens Z)ᵒᵖ) (a : ↥(O.obj.obj V)) :
    (((sqZeroInl O N).hom.app V).hom a).snd = 0 :=
  TrivSqZeroExt.snd_inl _ _

section Derivations

variable {O₀ : TopCat.Sheaf CommRingCat.{u} Z}

/-- The component over one open of the morphism of sheaves of commutative rings attached to a
relative derivation. -/
noncomputable def sqZeroSectionApp (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom)
    (V : (Opens Z)ᵒᵖ) : O.obj.obj V ⟶ (sqZeroPresheaf O N).obj V :=
  CommRingCat.ofHom (sqZeroRingHom (RingHom.id ↥(O.obj.obj V)) δ.d fun a b ↦ δ.d_mul a b)

/-- The first component of `sqZeroSectionApp` at `a` is `a`. -/
@[simp]
theorem sqZeroSectionApp_apply_fst (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom)
    (V : (Opens Z)ᵒᵖ) (a : ↥(O.obj.obj V)) :
    ((sqZeroSectionApp O N psi δ V).hom a).fst = a :=
  (sqZeroRingHom_fst _ _ (fun a b ↦ δ.d_mul a b) a).trans (RingHom.id_apply a)

/-- The second component of `sqZeroSectionApp` at `a` is `δ a`. -/
@[simp]
theorem sqZeroSectionApp_apply_snd (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom)
    (V : (Opens Z)ᵒᵖ) (a : ↥(O.obj.obj V)) :
    ((sqZeroSectionApp O N psi δ V).hom a).snd = δ.d a :=
  sqZeroRingHom_snd _ _ (fun a b ↦ δ.d_mul a b) a

/-- **A relative derivation read as a section of the square-zero extension.** For a derivation
`δ` of `O` relative to `psi` with values in `N`, the map `a ↦ (a, δ a)` is a morphism of sheaves
of commutative rings `O ⟶ O ⋉ N`: multiplicativity is exactly the Leibniz rule and naturality is
exactly compatibility with restriction. -/
noncomputable def sqZeroSectionOfDerivation (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom) :
    O ⟶ sqZeroSheaf O N :=
  ObjectProperty.homMk
    { app := sqZeroSectionApp O N psi δ
      naturality := fun V V' h ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦ by
        change (sqZeroSectionApp O N psi δ V').hom ((O.obj.map h).hom a)
            = ((sqZeroPresheaf O N).map h).hom ((sqZeroSectionApp O N psi δ V).hom a)
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · exact (sqZeroSectionApp_apply_snd O N psi δ V' _).trans
            ((δ.d_map h a).trans
              ((sqZeroPresheaf_map_snd O N h _).trans
                (congrArg (sectionRestrict N h)
                  (sqZeroSectionApp_apply_snd O N psi δ V a))).symm)) }

/-- The component of `sqZeroSectionOfDerivation` over `V` is `sqZeroSectionApp`. -/
@[simp]
theorem sqZeroSectionOfDerivation_app (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom)
    (V : (Opens Z)ᵒᵖ) :
    (sqZeroSectionOfDerivation O N psi δ).hom.app V = sqZeroSectionApp O N psi δ V :=
  rfl

/-- The section attached to a derivation splits the projection to the base. -/
theorem sqZeroSectionOfDerivation_comp_proj (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom) :
    sqZeroSectionOfDerivation O N psi δ ≫ sqZeroProj O N = 𝟙 O :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦
    sqZeroSectionApp_apply_fst O N psi δ V a)))

/-- The section attached to a derivation is trivial on the base of the derivation. -/
theorem sqZeroSectionOfDerivation_triv (psi : O₀ ⟶ O)
    (δ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom) :
    psi ≫ sqZeroSectionOfDerivation O N psi δ = psi ≫ sqZeroInl O N :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ CommRingCat.hom_ext (RingHom.ext fun y ↦
    TrivSqZeroExt.ext
      ((sqZeroSectionApp_apply_fst O N psi δ V _).trans
        (sqZeroInl_app_apply_fst O N V _).symm)
      ((sqZeroSectionApp_apply_snd O N psi δ V _).trans
        ((δ.d_app y).trans (sqZeroInl_app_apply_snd O N V _).symm)))))

/-- The second component of a splitting of the square-zero extension satisfies the Leibniz
rule, because the first component is the identity. -/
theorem sqZeroSectionSnd_mul (s : O ⟶ sqZeroSheaf O N) (hsplit : s ≫ sqZeroProj O N = 𝟙 O)
    {V : (Opens Z)ᵒᵖ} (a b : ↥(O.obj.obj V)) :
    ((s.hom.app V).hom (a * b)).snd
      = a • ((s.hom.app V).hom b).snd + b • ((s.hom.app V).hom a).snd := by
  have hfst : ∀ x : ↥(O.obj.obj V), ((s.hom.app V).hom x).fst = x := fun x ↦
    congrArg (fun m : O ⟶ O ↦ ((m.hom.app V).hom x)) hsplit
  refine (congrArg TrivSqZeroExt.snd (map_mul (s.hom.app V).hom a b)).trans ?_
  refine (TrivSqZeroExt.snd_mul ((s.hom.app V).hom a) ((s.hom.app V).hom b)).trans ?_
  simp only [hfst, op_smul_eq_smul]

/-- The second component of a morphism into the square-zero extension is compatible with
restriction. -/
theorem sqZeroSectionSnd_map (s : O ⟶ sqZeroSheaf O N) {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    (x : ↥(O.obj.obj V)) :
    ((s.hom.app V').hom ((O.obj.map h).hom x)).snd
      = sectionRestrict N h ((s.hom.app V).hom x).snd := by
  have hnat : (s.hom.app V').hom ((O.obj.map h).hom x)
      = ((sqZeroPresheaf O N).map h).hom ((s.hom.app V).hom x) :=
    congrArg (fun m : O.obj.obj V ⟶ (sqZeroSheaf O N).obj.obj V' ↦ m.hom x)
      (s.hom.naturality h)
  exact (congrArg TrivSqZeroExt.snd hnat).trans
    (sqZeroPresheaf_map_snd O N h ((s.hom.app V).hom x))

/-- The second component of a splitting of the square-zero extension which is trivial on the
base vanishes on the image of the base. -/
theorem sqZeroSectionSnd_app (psi : O₀ ⟶ O) (s : O ⟶ sqZeroSheaf O N)
    (htriv : psi ≫ s = psi ≫ sqZeroInl O N) {V : (Opens Z)ᵒᵖ} (y : ↥(O₀.obj.obj V)) :
    ((s.hom.app V).hom ((psi.hom.app V).hom y)).snd = 0 := by
  have h : ((psi ≫ s).hom.app V).hom y = ((psi ≫ sqZeroInl O N).hom.app V).hom y :=
    congrArg (fun m : O₀ ⟶ sqZeroSheaf O N ↦ ((m.hom.app V).hom y)) htriv
  exact (congrArg TrivSqZeroExt.snd h).trans (sqZeroInl_app_apply_snd O N V _)

/-- **A splitting of the square-zero extension read as a relative derivation.** A morphism of
sheaves of commutative rings `s : O ⟶ O ⋉ N` which splits the projection and is trivial on the
base of `psi` has second component a derivation of `O` relative to `psi`. -/
@[ega "IV 16.5.1" "Direction"]
noncomputable def derivationOfSqZeroSection (psi : O₀ ⟶ O) (s : O ⟶ sqZeroSheaf O N)
    (hsplit : s ≫ sqZeroProj O N = 𝟙 O) (htriv : psi ≫ s = psi ≫ sqZeroInl O N) :
    PresheafOfModulesOfCommRing.Derivation' N.val psi.hom where
  d {V} := (TrivSqZeroExt.sndHom ↥(O.obj.obj V) ↥(N.val.obj V)).toAddMonoidHom.comp
    (s.hom.app V).hom.toAddMonoidHom
  d_mul a b := sqZeroSectionSnd_mul O N s hsplit a b
  d_map h x := sqZeroSectionSnd_map O N s h x
  d_app y := sqZeroSectionSnd_app O N psi s htriv y

/-- The derivation attached to a splitting `s` sends `a` to the second component of `s a`. -/
@[simp]
theorem derivationOfSqZeroSection_d (psi : O₀ ⟶ O) (s : O ⟶ sqZeroSheaf O N)
    (hsplit : s ≫ sqZeroProj O N = 𝟙 O) (htriv : psi ≫ s = psi ≫ sqZeroInl O N)
    {V : (Opens Z)ᵒᵖ} (a : ↥(O.obj.obj V)) :
    (derivationOfSqZeroSection O N psi s hsplit htriv).d a = ((s.hom.app V).hom a).snd :=
  rfl

/-- A relative derivation is determined by the values of its underlying additive maps. -/
theorem derivation_ext (psi : O₀ ⟶ O)
    {δ₁ δ₂ : PresheafOfModulesOfCommRing.Derivation' N.val psi.hom}
    (h : ∀ (V : (Opens Z)ᵒᵖ) (a : ↥(O.obj.obj V)), δ₁.d a = δ₂.d a) : δ₁ = δ₂ :=
  PresheafOfModulesOfCommRing.Derivation.ext (funext fun V ↦ AddMonoidHom.ext (h V))

end Derivations

end AlgebraicGeometry.SheafOfModules

end
