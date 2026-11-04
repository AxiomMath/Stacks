module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Epimorphisms of sheaves of modules are locally surjective

Let `J` be a Grothendieck topology on a category `C` and let `R : Sheaf J RingCat` be a sheaf of
rings. A morphism of sheaves of `R`-modules which is locally surjective is an epimorphism with no
hypothesis at all; the converse is `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`
under `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat`. This file
proves the converse from the *existence of an abelian structure* on `SheafOfModules.{t} R` alone,
which is strictly weaker: the two sheafification hypotheses produce such a structure but are not
produced by one.

The point is that no sheafification is needed to form the image: the sections of the target
which locally lie in the range of `f` form a submodule, and it is automatically a *sheaf* of
modules, being a subsheaf of a sheaf cut out by a local condition. So `f` factors through a
subobject of its target, which is therefore both a monomorphism and (if `f` is an epimorphism)
an epimorphism, hence an isomorphism because an abelian category is balanced. That forces every
section of the target to lie locally in the range.

For a *monomorphism* no sheafification is needed at all: its pointwise range is already a sheaf,
being isomorphic as a presheaf of modules to the source. So every monomorphism into a sheaf of
modules, and so every subobject of one, is the inclusion of a `SheafOfModules.Submodule`.

## Main definitions

* `rangeSubmodule`: the pointwise range of a morphism of sheaves of modules, as a submodule of
  the underlying presheaf of modules of the target.
* `localImage`, `imageSubmodule`: the sections of the target which locally lie in the range, as
  a submodule of the underlying presheaf of modules and as a `SheafOfModules.Submodule`.
* `monoRangeSubmodule`: for a monomorphism, its pointwise range as a
  `SheafOfModules.Submodule` of the target, and `monoRangeSubmoduleIso` the identification of
  the source with it.

## Main results

* `isLocallySurjective_of_epi`: an epimorphism of sheaves of modules is locally surjective.
* `balanced_of_abelian`: a category of sheaves of modules carrying an abelian structure is
  balanced.
* `exists_submodule_iso_of_mono`: **every monomorphism into a sheaf of modules is, up to an
  isomorphism over the target, the inclusion of a submodule.**
* `subobject_mk_monoRangeSubmodule_ι` and `submodule_eq_of_subobject_mk_ι_eq`: **`N ↦
  Subobject.mk N.ι` is a bijection from the submodules of a sheaf of modules to its
  subobjects.**
* `submodule_eq_of_subobject_mk_ι_comp_eq` and `exists_submodule_of_subobject_comp_iso`: the
  same bijection read through an isomorphism `N ≅ P` of the ambient module, with the
  identification of the two quotients that transports conditions imposed on them.

## Implementation notes

`Mathlib.CategoryTheory.Sites.Subsheaf` already has the subfunctor of local sections,
`Subfunctor.sheafify`, together with its functoriality and its idempotence on a sheaf; the work
here is to see that it is a submodule when the subfunctor is one, which is the closure of the
local-membership condition under addition and under multiplication by a section of `R` — both
come from `GrothendieckTopology.superset_covering` applied to the sieve of a summand.

Both `balanced_of_abelian` and the uses of the abelian structure below have to hand the
preadditive structure to instance search as a local instance. The reason is a genuine diamond:
`SheafOfModules.instPreadditive` is a global instance, so the search for the
`HasZeroMorphisms (SheafOfModules R)` argument of `IsNormalEpiCategory` finds it, while the
normality fields of an abelian structure supplied as a hypothesis are stated relative to that
structure's own preadditive part. The two agree -- `Preadditive` is a subsingleton in the
presence of binary biproducts -- but not syntactically, so the search for `Balanced` fails
unless the abelian structure's preadditive part is made the ambient one.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (1)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u u' t

namespace Stacks.SheafOfModules.ImageSubsheaf

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{t} R}

/-- The pointwise range of a morphism of sheaves of modules, as a submodule of the underlying
presheaf of modules of the target. -/
noncomputable def rangeSubmodule (f : M ⟶ N) : N.val.Submodule where
  obj X := LinearMap.range (f.val.app X).hom
  map {X Y} g := by
    rintro x ⟨m, rfl⟩
    exact ⟨M.val.map g m, PresheafOfModules.naturality_apply f.val g m⟩

/-- Membership in the pointwise range is being in the image of `f` on sections. -/
lemma mem_rangeSubmodule_obj_iff (f : M ⟶ N) (X : Cᵒᵖ) (s : N.val.obj X) :
    s ∈ (rangeSubmodule f).obj X ↔ ∃ m, f.val.app X m = s := Iff.rfl

/-- An arrow lies in the sieve of local membership in the range exactly when the restriction of
the section along it is in the range. -/
lemma sieveOfSection_rangeSubmodule_apply (f : M ⟶ N) {X : Cᵒᵖ} (s : N.val.obj X) {V : C}
    (g : V ⟶ X.unop) :
    (rangeSubmodule f).toSubfunctor.sieveOfSection s g ↔
      N.val.map g.op s ∈ (rangeSubmodule f).obj (op V) :=
  Iff.rfl

/-- The submodule of sections of `N` over `X` which locally lie in the range of `f`. -/
noncomputable def localImageObj (f : M ⟶ N) (X : Cᵒᵖ) :
    Submodule (R.obj.obj X) (N.val.obj X) where
  carrier := {s | (rangeSubmodule f).toSubfunctor.sieveOfSection s ∈ J X.unop}
  zero_mem' := by
    refine J.superset_covering ?_ (J.top_mem X.unop)
    intro V g _
    rw [sieveOfSection_rangeSubmodule_apply, map_zero]
    exact Submodule.zero_mem _
  add_mem' := fun {s} {t} hs ht => by
    refine J.superset_covering ?_ (J.intersection_covering hs ht)
    rintro V g ⟨hg1, hg2⟩
    rw [sieveOfSection_rangeSubmodule_apply] at hg1 hg2 ⊢
    rw [map_add]
    exact Submodule.add_mem _ hg1 hg2
  smul_mem' := fun r s hs => by
    refine J.superset_covering ?_ hs
    intro V g hg
    rw [sieveOfSection_rangeSubmodule_apply] at hg ⊢
    rw [PresheafOfModules.map_smul]
    exact Submodule.smul_mem _ (R.obj.map g.op r) hg

/-- Membership in the local image is the covering of the sieve of local membership in the
range. -/
lemma mem_localImageObj_iff (f : M ⟶ N) {X : Cᵒᵖ} (s : N.val.obj X) :
    s ∈ localImageObj f X ↔ (rangeSubmodule f).toSubfunctor.sieveOfSection s ∈ J X.unop :=
  Iff.rfl

/-- The local image of a morphism of sheaves of modules: the sections of the target which
locally lie in the range. -/
noncomputable def localImage (f : M ⟶ N) : N.val.Submodule where
  obj := localImageObj f
  map g := fun _ hs => ((rangeSubmodule f).toSubfunctor.sheafify J).map g hs

/-- Membership in the local image, as a submodule of the presheaf of modules. -/
lemma mem_localImage_obj_iff (f : M ⟶ N) {X : Cᵒᵖ} (s : N.val.obj X) :
    s ∈ (localImage f).obj X ↔ (rangeSubmodule f).toSubfunctor.sieveOfSection s ∈ J X.unop :=
  Iff.rfl

/-- The local image is the sheafification, as a subfunctor, of the pointwise range. -/
lemma toSubfunctor_localImage (f : M ⟶ N) :
    (localImage f).toSubfunctor = (rangeSubmodule f).toSubfunctor.sheafify J := by
  ext X s
  exact mem_localImage_obj_iff f s

/-- The underlying type-valued presheaf of a sheaf of modules is a sheaf. -/
lemma isSheaf_forget (N : SheafOfModules.{t} R) :
    Presieve.IsSheaf J (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{t}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf

/-- The local image of a morphism of sheaves of modules, as a submodule of the sheaf of
modules `N`. -/
noncomputable def imageSubmodule (f : M ⟶ N) : N.Submodule where
  toSubmodule := localImage f
  isSheaf {X} s hs := by
    rw [toSubfunctor_localImage] at hs
    have h2 : s ∈ (((rangeSubmodule f).toSubfunctor.sheafify J).sheafify J).obj X := hs
    rw [Subfunctor.sheafify_sheafify (J := J) (G := (rangeSubmodule f).toSubfunctor)
      (isSheaf_forget N)] at h2
    exact h2

/-- A section in the range of `f` lies in the local image of `f`. -/
lemma apply_mem_imageSubmodule (f : M ⟶ N) {X : Cᵒᵖ} (m : M.val.obj X) :
    f.val.app X m ∈ (imageSubmodule f).obj X := by
  refine J.superset_covering ?_ (J.top_mem X.unop)
  intro V g _
  exact (rangeSubmodule f).map g.op ⟨m, rfl⟩

/-- If `f` is an epimorphism, so is the inclusion of its local image. -/
lemma epi_imageSubmodule_ι (f : M ⟶ N) [Epi f] : Epi (imageSubmodule f).ι := by
  constructor
  intro P a b h
  refine (cancel_epi f).1 ?_
  ext X m
  exact congr($(h).val.app X ⟨f.val.app X m, apply_mem_imageSubmodule f m⟩)

/-- A category of sheaves of modules carrying an abelian structure is balanced. -/
lemma balanced_of_abelian [Abelian (SheafOfModules.{t} R)] :
    Balanced (SheafOfModules.{t} R) := by
  let : Preadditive (SheafOfModules.{t} R) := Abelian.toPreadditive
  exact inferInstance

/-- For an epimorphism `f`, the inclusion of the local image of `f` is an isomorphism. -/
lemma isIso_imageSubmodule_ι [Abelian (SheafOfModules.{t} R)] (f : M ⟶ N) [Epi f] :
    IsIso (imageSubmodule f).ι :=
  have := epi_imageSubmodule_ι f
  have := balanced_of_abelian (R := R)
  isIso_of_mono_of_epi _

/-- **An epimorphism of sheaves of modules is locally surjective**, with no hypothesis beyond
an abelian structure on the category of sheaves of modules. -/
theorem isLocallySurjective_of_epi [Abelian (SheafOfModules.{t} R)] (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) where
  imageSieve_mem {U} s := by
    have := isIso_imageSubmodule_ι f
    obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.forget R ⋙
        PresheafOfModules.evaluation R.obj (op U)).map (imageSubmodule f).ι)).2 s
    have hmem : s ∈ (imageSubmodule f).obj (op U) := hy ▸ y.2
    exact J.superset_covering (fun _ _ hg => hg) hmem

/-! ### The range of a monomorphism, and subobjects as submodules -/

section Mono

variable (f : M ⟶ N) [Mono f]

/-- **The factorization of a morphism of sheaves of modules through its pointwise range**, as a
morphism of presheaves of modules: on sections it is the range restriction. -/
noncomputable def toRangeSubmoduleHom : M.val ⟶ (rangeSubmodule f).toPresheafOfModules where
  app U := ModuleCat.ofHom (f.val.app U).hom.rangeRestrict
  naturality {U V} g := by
    ext x
    exact Subtype.ext (PresheafOfModules.naturality_apply f.val g x)

omit [Mono f] in
/-- The factorization through the pointwise range, followed by the inclusion of the range, is
`f`. -/
@[simp]
theorem toRangeSubmoduleHom_comp_ι :
    toRangeSubmoduleHom f ≫ (rangeSubmodule f).ι = f.val := by
  apply PresheafOfModules.Hom.ext
  ext U x
  rfl

/-- **The factorization of a monomorphism through its pointwise range is an isomorphism.** -/
instance isIso_toRangeSubmoduleHom : IsIso (toRangeSubmoduleHom f) := by
  have : Mono f.val := inferInstanceAs (Mono ((SheafOfModules.forget R).map f))
  have : Mono (toRangeSubmoduleHom f) :=
    PresheafOfModules.mono_of_injective
      fun U x y hxy => PresheafOfModules.injective_of_mono f.val U (congrArg Subtype.val hxy)
  have : Epi (toRangeSubmoduleHom f) :=
    PresheafOfModules.epi_of_surjective fun U => by
      rintro ⟨y, x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  exact isIso_of_mono_of_epi _

/-- The pointwise range of a monomorphism of sheaves of modules is itself a sheaf: it is
isomorphic, as a presheaf of modules, to the source. -/
theorem isSheaf_rangeSubmodule :
    Presheaf.IsSheaf J (rangeSubmodule f).toPresheafOfModules.presheaf :=
  (Presheaf.isSheaf_of_iso_iff
      ((PresheafOfModules.toPresheaf R.obj).mapIso (asIso (toRangeSubmoduleHom f)))).mp M.isSheaf

/-- **The range of a monomorphism of sheaves of modules, as a submodule of its target.** -/
@[sga "2 XIV 1.8.2.1" "special case"]
noncomputable def monoRangeSubmodule : N.Submodule where
  toSubmodule := rangeSubmodule f
  isSheaf := by
    have hP : Presieve.IsSheaf J (rangeSubmodule f).toSubfunctor.toFunctor := by
      change Presieve.IsSheaf J ((rangeSubmodule f).toPresheafOfModules.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{t})
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ (isSheaf_rangeSubmodule f)
    exact fun {_} => ((rangeSubmodule f).toSubfunctor.isSheaf_iff (isSheaf_forget N)).mp hP _

/-- The factorization of a monomorphism through its range, as a morphism of sheaves of
modules. -/
noncomputable def toMonoRangeSubmodule : M ⟶ (monoRangeSubmodule f).toSheafOfModules :=
  ⟨toRangeSubmoduleHom f⟩

/-- The factorization of a monomorphism through its range is an isomorphism of sheaves of
modules. -/
instance isIso_toMonoRangeSubmodule : IsIso (toMonoRangeSubmodule f) := by
  apply (isIso_iff_of_reflects_iso (toMonoRangeSubmodule f) (SheafOfModules.forget R)).mp
  change IsIso (toRangeSubmoduleHom f)
  infer_instance

/-- **A monomorphism of sheaves of modules identifies its source with a submodule of its
target.** -/
noncomputable def monoRangeSubmoduleIso : M ≅ (monoRangeSubmodule f).toSheafOfModules :=
  asIso (toMonoRangeSubmodule f)

/-- That identification carries the inclusion of the submodule to `f`. -/
@[simp]
theorem monoRangeSubmoduleIso_hom_comp_ι :
    (monoRangeSubmoduleIso f).hom ≫ (monoRangeSubmodule f).ι = f :=
  SheafOfModules.hom_ext (toRangeSubmoduleHom_comp_ι f)

/-- **Every monomorphism into a sheaf of modules is, up to an isomorphism over the target, the
inclusion of a submodule.** -/
theorem exists_submodule_iso_of_mono :
    ∃ (P : N.Submodule) (e : M ≅ P.toSheafOfModules), e.hom ≫ P.ι = f :=
  ⟨monoRangeSubmodule f, monoRangeSubmoduleIso f, monoRangeSubmoduleIso_hom_comp_ι f⟩

end Mono

/-- **Every subobject of a sheaf of modules is the subobject of a submodule**: the passage
`N ↦ Subobject.mk N.ι` from submodules to subobjects is surjective, with
`Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule` of the arrow as a section. -/
theorem subobject_mk_monoRangeSubmodule_ι (K : Subobject N) :
    Subobject.mk (monoRangeSubmodule K.arrow).ι = K :=
  (Subobject.mk_eq_mk_of_comm _ K.arrow (monoRangeSubmoduleIso K.arrow).symm
    ((Iso.inv_comp_eq _).2 (monoRangeSubmoduleIso_hom_comp_ι K.arrow).symm)).trans
    (Subobject.mk_arrow K)

/-- A submodule of a sheaf of modules is contained in another as soon as the subobjects their
inclusions define are: the comparison morphism of the subobjects carries a section of the first
to the same section of the target, which therefore lies in the second. -/
theorem submodule_le_of_subobject_mk_ι_le {N₁ N₂ : N.Submodule}
    (h : Subobject.mk N₁.ι ≤ Subobject.mk N₂.ι) : N₁ ≤ N₂ := by
  intro U s hs
  have hfac : Subobject.ofMkLEMk N₁.ι N₂.ι h ≫ N₂.ι = N₁.ι := Subobject.ofMkLEMk_comp h
  have ht : ((Subobject.ofMkLEMk N₁.ι N₂.ι h).val.app U ⟨s, hs⟩).val = s :=
    congrArg (fun q => q.val.app U ⟨s, hs⟩) hfac
  simpa [ht] using ((Subobject.ofMkLEMk N₁.ι N₂.ι h).val.app U ⟨s, hs⟩).property

/-- **Two submodules of a sheaf of modules defining the same subobject are equal**, so
`N ↦ Subobject.mk N.ι` is injective as well; together with
`Stacks.SheafOfModules.ImageSubsheaf.subobject_mk_monoRangeSubmodule_ι` it is a bijection between
the submodules of a sheaf of modules and its subobjects. -/
theorem submodule_eq_of_subobject_mk_ι_eq {N₁ N₂ : N.Submodule}
    (h : Subobject.mk N₁.ι = Subobject.mk N₂.ι) : N₁ = N₂ :=
  le_antisymm (submodule_le_of_subobject_mk_ι_le (le_of_eq h))
    (submodule_le_of_subobject_mk_ι_le (le_of_eq h.symm))

/-! ### The bijection read through an isomorphism of the ambient module -/

/-- **Two submodules whose inclusions, followed by an isomorphism of the ambient module, define
the same subobject are equal.** -/
theorem submodule_eq_of_subobject_mk_ι_comp_eq {P : SheafOfModules.{t} R} (i : N ≅ P)
    {N₁ N₂ : N.Submodule}
    (h : Subobject.mk (N₁.ι ≫ i.hom) = Subobject.mk (N₂.ι ≫ i.hom)) : N₁ = N₂ := by
  refine submodule_eq_of_subobject_mk_ι_eq ?_
  refine Subobject.mk_eq_mk_of_comm _ _
    (Subobject.isoOfMkEqMk (N₁.ι ≫ i.hom) (N₂.ι ≫ i.hom) h) ?_
  refine (cancel_mono i.hom).mp ?_
  exact (Category.assoc _ _ _).trans (Subobject.ofMkLEMk_comp h.le)

/-- **Every subobject of `N` is the inclusion of a submodule of `P`, read backwards through an
isomorphism `i : N ≅ P`, and the two quotients agree.** -/
theorem exists_submodule_of_subobject_comp_iso [Abelian (SheafOfModules.{t} R)]
    {P : SheafOfModules.{t} R} (i : N ≅ P) (K : Subobject N) :
    ∃ Q : P.Submodule, Subobject.mk (Q.ι ≫ i.inv) = K ∧
      Nonempty (cokernel Q.ι ≅ cokernel K.arrow) := by
  set w := monoRangeSubmoduleIso (K.arrow ≫ i.hom) with hwdef
  have hI : (monoRangeSubmodule (K.arrow ≫ i.hom)).ι = w.inv ≫ (K.arrow ≫ i.hom) :=
    ((Iso.inv_comp_eq w).2 (monoRangeSubmoduleIso_hom_comp_ι (K.arrow ≫ i.hom)).symm).symm
  have hcomm : w.symm.hom ≫ K.arrow =
      (monoRangeSubmodule (K.arrow ≫ i.hom)).ι ≫ i.inv := by
    rw [hI]
    simp
  refine ⟨monoRangeSubmodule (K.arrow ≫ i.hom),
    (Subobject.mk_eq_mk_of_comm _ K.arrow w.symm hcomm).trans (Subobject.mk_arrow K), ⟨?_⟩⟩
  exact cokernelIsoOfEq hI ≪≫ cokernelEpiComp w.inv (K.arrow ≫ i.hom) ≪≫
    cokernelCompIsIso K.arrow i.hom

end Stacks.SheafOfModules.ImageSubsheaf

end
