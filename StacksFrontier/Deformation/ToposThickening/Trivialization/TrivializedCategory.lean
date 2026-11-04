module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# The category of trivialized first order thickenings of a ringed topos

A first order thickening of ringed topoi is *trivial* when its inclusion admits a retraction,
and a *trivialization* is a choice of such a retraction. The underlying morphism of topoi of a
thickening is an equivalence, and a trivialization splits the structure-sheaf map, so a
trivialized first order thickening of `(Sh(C), O)` is the same data as a sheaf of commutative
rings `A` on `C`, a surjection `A ⟶ O` with square-zero kernel, and a chosen section of that
surjection. This file takes that data as the objects of the category of trivialized first order
thickenings of `(Sh(C), O)`, with the maps of structure sheaves commuting with the surjections
and the sections as its morphisms, and builds the ideal of such a thickening as a sheaf of
`O`-modules.

## Main definitions

* `Deformation.ToposThickening.TrivializedThickening`: a trivialized first order thickening of
  a ringed topos, presented on the site of the ringed topos.
* `Deformation.ToposThickening.TrivializedThickening.Hom` and the `Category` instance on
  `TrivializedThickening`.
* `Deformation.ToposThickening.TrivializedThickening.idealSections`: the local sections killed
  by the surjection, as an ideal of the structure sheaf of the thickening.
* `Deformation.ToposThickening.TrivializedThickening.ideal`: the same, as a sheaf of
  `O`-modules, the action being multiplication by the lift under the trivialization.

## Main results

* `Deformation.ToposThickening.TrivializedThickening.isSheaf_idealPresheaf`: the ideal is a
  sheaf of abelian groups.

## Variance

**The Hom of this category runs in the algebraic direction**: a morphism `T ⟶ S` is a morphism
`A_T ⟶ A_S` of sheaves of commutative rings, the direction of `h^♯`. The source's morphism of
trivialized first order thickenings of `(Sh(C), O)` is a morphism of ringed topoi
`h : (Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂)` with `π₂ ∘ h = π₁` (Stacks 08MK), whose `h^♯` goes
`O'₂ ⟶ O'₁` (Stacks 08MJ), so **this category is the opposite of the source's**: such an `h` is
a morphism of this category out of the thickening it lands in and into the one it leaves. That
is why `Deformation.ToposThickening.TrivializedThickening.moduleEquivalence` states Stacks 08MG
with no `ᵒᵖ` on the module side, while its ringed space sibling
`AlgebraicGeometry.RingedSpaceThickening.trivializedThickeningEquivalence` (Stacks 08L9), whose
category keeps the geometric Hom, carries one. The two are the same statement; see the
"## Variance" section of
`StacksFrontier/Deformation/ToposThickening/Trivialization/ModuleEquivalence.lean`.

## Implementation notes

The surjectivity required of a first order thickening is not part of the data: the structure
map of an object here has a section, hence is surjective on every object of the site, hence is
locally surjective. What remains of the first order condition is that its kernel has square
zero, which is the field `sq_zero`.

Thickenings are presented on the site `C` of the ringed topos itself rather than on an
arbitrary site `D` equivalent to it. Nothing is lost: the direct image of a first order
thickening is an equivalence of topoi, so a thickening on `D` is carried to one on `D` over the
transported structure sheaf, and
`Deformation.ToposThickening.trivializedThickeningOfTrivialization` performs exactly that
transport for the general notion of `Deformation.ToposThickening.Trivialization`. Presenting
them this way is what makes the collection a category at all: morphisms of ringed topoi do not
form a category — `AlgebraicGeometry.RingedToposHom.comp` has no identity and associativity
laws on the nose, see the implementation notes of
`StacksFrontier/Deformation/ToposThickening/Trivialization/RingedToposId.lean` — whereas morphisms
of sheaves of commutative rings on a fixed site do.

The ideal is built by hand rather than as a categorical kernel: its module structure is over
`O`, not over the structure sheaf of the thickening, and that structure is the one the
trivialization provides, through `Module.compHom` along the section.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ) — `h^♯` induces
  `ℐ₂ ⟶ ℐ₁`
* [Stacks Project, Tag 08MK](https://stacks.math.columbia.edu/tag/08MK) — what a morphism of
  trivialized first order thickenings is
-/

@[expose] public section

open CategoryTheory

universe u

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{u}}

/-- A trivialized first order thickening of the ringed topos `(Sh(C), O)`, presented on the
site `C`: a sheaf of commutative rings `A` with a surjection onto `O` whose kernel has square
zero, together with a chosen splitting of that surjection. -/
@[stacks 08MG "the category of trivialized first order thickenings: objects"]
structure TrivializedThickening (O : Sheaf J CommRingCat.{u}) where
  /-- The structure sheaf of the thickening. -/
  A : Sheaf J CommRingCat.{u}
  /-- The surjection onto the structure sheaf of the thickened ringed topos. -/
  proj : A ⟶ O
  /-- The trivialization: a splitting of the surjection. -/
  split : O ⟶ A
  /-- The splitting is a section of the surjection. -/
  split_proj : split ≫ proj = 𝟙 O
  /-- The kernel of the surjection has square zero. -/
  sq_zero : ∀ (U : Cᵒᵖ) (x y : A.obj.obj U),
    (proj.hom.app U).hom x = 0 → (proj.hom.app U).hom y = 0 → x * y = 0

namespace TrivializedThickening

/-- The splitting is a section of the surjection, on local sections. -/
@[simp]
theorem proj_split_apply (T : TrivializedThickening O) (U : Cᵒᵖ) (a : O.obj.obj U) :
    (T.proj.hom.app U).hom ((T.split.hom.app U).hom a) = a := by
  have h := congrArg (fun φ : O ⟶ O => (φ.hom.app U).hom a) T.split_proj
  simpa using h

/-- A morphism of trivialized first order thickenings: a morphism of the structure sheaves
compatible with both the surjections and the trivializations.

This runs in the algebraic direction, that of `h^♯`. The source's morphism of trivialized
thickenings is a morphism of ringed topoi `h : (Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂)` over
`(Sh(C), O)` (Stacks 08MK), so a `Hom T S` here is such an `h` with `T` the *target* of `h` and
`S` its source, and this category is the opposite of the source's. See the "## Variance"
section of this module. -/
@[ext, stacks 08MG "the category of trivialized first order thickenings: morphisms, in the \
algebraic direction A_T ⟶ A_S (the opposite of the source's ringed-topos morphisms of \
Stacks 08MK)"]
structure Hom (T S : TrivializedThickening O) where
  /-- The morphism of structure sheaves. -/
  hom : T.A ⟶ S.A
  /-- Compatibility with the surjections. -/
  hom_proj : hom ≫ S.proj = T.proj
  /-- Compatibility with the trivializations. -/
  split_hom : T.split ≫ hom = S.split

/-- Trivialized first order thickenings form a category, with the morphisms `Hom`. -/
instance : Category (TrivializedThickening O) where
  Hom T S := Hom T S
  id T := ⟨𝟙 T.A, Category.id_comp _, Category.comp_id _⟩
  comp {T S R} f g :=
    ⟨f.hom ≫ g.hom, by rw [Category.assoc, g.hom_proj, f.hom_proj],
      by rw [← Category.assoc, f.split_hom, g.split_hom]⟩

/-- The identity of a trivialized thickening is the identity of its structure sheaf. -/
@[simp]
theorem id_hom (T : TrivializedThickening O) : Hom.hom (𝟙 T) = 𝟙 T.A := rfl

/-- Composition of morphisms of trivialized thickenings is composition of the morphisms of
structure sheaves. -/
@[simp, reassoc]
theorem comp_hom {T S R : TrivializedThickening O} (f : T ⟶ S) (g : S ⟶ R) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Morphisms of trivialized thickenings with the same morphism of structure sheaves are
equal. -/
theorem hom_ext {T S : TrivializedThickening O} {f g : T ⟶ S} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

section Ideal

variable (T : TrivializedThickening O)

/-- The ideal of the thickening: the local sections of `A` killed by the surjection. -/
def idealSections (U : Cᵒᵖ) : Ideal (T.A.obj.obj U) := RingHom.ker (T.proj.hom.app U).hom

/-- A local section lies in the ideal exactly when the surjection kills it. -/
theorem mem_idealSections {U : Cᵒᵖ} {x : T.A.obj.obj U} :
    x ∈ T.idealSections U ↔ (T.proj.hom.app U).hom x = 0 := Iff.rfl

/-- The structure sheaf of the thickened ringed topos acts on the ideal through the
trivialization. -/
noncomputable instance idealModule (U : Cᵒᵖ) : Module (O.obj.obj U) (T.idealSections U) :=
  Module.compHom _ (T.split.hom.app U).hom

/-- The action of `O` on the ideal is multiplication by the lift under the trivialization. -/
theorem idealSections_smul_coe {U : Cᵒᵖ} (a : O.obj.obj U) (x : T.idealSections U) :
    ((a • x : T.idealSections U) : T.A.obj.obj U) =
      (T.split.hom.app U).hom a * (x : T.A.obj.obj U) := rfl

/-- The surjection commutes with the restriction maps, on local sections. -/
theorem proj_naturality_apply {U V : Cᵒᵖ} (f : U ⟶ V) (x : T.A.obj.obj U) :
    (T.proj.hom.app V).hom ((T.A.obj.map f).hom x) =
      (O.obj.map f).hom ((T.proj.hom.app U).hom x) :=
  congrArg (fun g : T.A.obj.obj U ⟶ O.obj.obj V => g.hom x) (T.proj.hom.naturality f)

/-- The trivialization commutes with the restriction maps, on local sections. -/
theorem split_naturality_apply {U V : Cᵒᵖ} (f : U ⟶ V) (a : O.obj.obj U) :
    (T.A.obj.map f).hom ((T.split.hom.app U).hom a) =
      (T.split.hom.app V).hom ((O.obj.map f).hom a) :=
  (congrArg (fun g : O.obj.obj U ⟶ T.A.obj.obj V => g.hom a) (T.split.hom.naturality f)).symm

/-- The restriction maps of `A` carry the ideal into the ideal. -/
noncomputable def idealRestriction {U V : Cᵒᵖ} (f : U ⟶ V) :
    T.idealSections U →+ T.idealSections V where
  toFun x := ⟨(T.A.obj.map f).hom x.1, by
    rw [T.mem_idealSections, T.proj_naturality_apply f x.1, x.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- `idealRestriction` is the restriction map of `A` on the underlying sections. -/
@[simp]
theorem idealRestriction_coe {U V : Cᵒᵖ} (f : U ⟶ V) (x : T.idealSections U) :
    ((T.idealRestriction f x : T.idealSections V) : T.A.obj.obj V) =
      (T.A.obj.map f).hom (x : T.A.obj.obj U) := rfl

/-- The ideal of the thickening, as a presheaf of abelian groups. -/
noncomputable def idealPresheaf : Cᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (T.idealSections U)
  map f := AddCommGrpCat.ofHom (T.idealRestriction f)
  map_id U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    change (T.A.obj.map (𝟙 U)).hom x.1 = x.1
    rw [T.A.obj.map_id]
    rfl
  map_comp f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    change (T.A.obj.map (f ≫ g)).hom x.1 = (T.A.obj.map g).hom ((T.A.obj.map f).hom x.1)
    rw [T.A.obj.map_comp]
    rfl

/-- The restriction maps of `idealPresheaf` are those of `A` on the underlying sections. -/
@[simp]
theorem idealPresheaf_map_coe {U V : Cᵒᵖ} (f : U ⟶ V) (x : T.idealSections U) :
    (T.idealPresheaf.map f x).1 = (T.A.obj.map f).hom x.1 := rfl

/-- The ideal of the thickening is a sheaf of abelian groups: a compatible family of ideal
sections glues in `A`, and the glued section is killed by the surjection because `O` is
separated. -/
theorem isSheaf_idealPresheaf : Presheaf.IsSheaf J T.idealPresheaf := by
  have happ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : O.obj.obj U),
      (O.obj ⋙ CategoryTheory.forget CommRingCat).map f a = (O.obj.map f).hom a :=
    fun _ _ => rfl
  have hsheaf : ∀ F : Sheaf J CommRingCat.{u},
      Presieve.IsSheaf J (F.obj ⋙ CategoryTheory.forget CommRingCat) := fun F =>
    (isSheaf_iff_isSheaf_of_type (J := J) _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget (J := J) (P' := F.obj)
        (CategoryTheory.forget CommRingCat)).mp F.property)
  rw [Presheaf.isSheaf_iff_isSheaf_forget (J := J) (P' := T.idealPresheaf)
    (CategoryTheory.forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  intro Y S hS x hx
  let xA : Presieve.FamilyOfElements (T.A.obj ⋙ CategoryTheory.forget CommRingCat) S.arrows :=
    fun _ f hf => (x f hf).1
  have hxA : xA.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ h =>
    congrArg Subtype.val (hx g₁ g₂ h₁ h₂ h)
  obtain ⟨t, ht, hu⟩ := hsheaf T.A S hS xA hxA
  have ht' : ∀ ⦃Z : C⦄ (f : Z ⟶ Y) (hf : S.arrows f),
      (T.A.obj.map f.op).hom t = (x f hf).1 := fun _ f hf => ht f hf
  have hker : (T.proj.hom.app (Opposite.op Y)).hom t = 0 := by
    refine (hsheaf O S hS).isSeparatedFor (fun _ _ _ => 0) _ 0 (fun Z f hf => ?_) fun Z f _ => ?_
    · change (O.obj ⋙ CategoryTheory.forget CommRingCat).map f.op
        ((T.proj.hom.app (Opposite.op Y)).hom t) = 0
      rw [happ f.op, ← T.proj_naturality_apply f.op t, ht' f hf]
      exact (x f hf).2
    · exact map_zero (O.obj.map f.op).hom
  refine ⟨⟨t, hker⟩, fun Z f hf => Subtype.ext ?_, fun s hs => Subtype.ext ?_⟩
  · exact ht' f hf
  · exact hu s.1 fun Z f hf => congrArg Subtype.val (hs f hf)

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The ideal of the thickening, as a presheaf of `O`-modules. -/
noncomputable def idealPresheafOfModules :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj := by
  letI inst : ∀ U : Cᵒᵖ,
      Module ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) (T.idealPresheaf.obj U) :=
    T.idealModule
  refine @PresheafOfModules.ofPresheaf _ _ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj
    T.idealPresheaf inst ?_
  intro U V f r z
  refine Subtype.ext ?_
  change (T.A.obj.map f).hom ((T.split.hom.app U).hom r * z.1) =
    (T.split.hom.app V).hom ((O.obj.map f).hom r) * (T.A.obj.map f).hom z.1
  rw [map_mul, T.split_naturality_apply f r]

/-- The ideal of the thickening, as a sheaf of `O`-modules: the kernel of the surjection,
with `O` acting through the trivialization. -/
noncomputable def ideal : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  ⟨T.idealPresheafOfModules, T.isSheaf_idealPresheaf⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The sections of `ideal` over `U` are the ideal sections `idealSections U`. -/
@[simp]
theorem ideal_val_obj (U : Cᵒᵖ) : (T.ideal.val.obj U : Type u) = T.idealSections U := rfl

end Ideal

end TrivializedThickening

end Deformation.ToposThickening

end
