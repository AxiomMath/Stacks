module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.SetTheory.Ordinal.Family
import StacksCore.Tactic.StacksAttribute

/-!
# A big abelian category with large Ext

There is an abelian category whose `Ext`-groups are not small: the category of
representations of the free monoid on the class of ordinals, with values in abelian groups.

The construction is Freyd's. For each ordinal `α` one builds a self-extension of the trivial
representation on `ℤ` by itself in which the generator indexed by `α` acts by the nilpotent
"shear" `biprod.snd ≫ biprod.inl` and every other generator acts by zero. Distinct ordinals
give extensions that are not isomorphic under the identity on the sub- and quotient objects,
so the Yoneda `Ext¹` between two copies of the trivial representation receives an injection
from the ordinals and therefore cannot be small.

## Main results

* `Stacks.Examples.exists_abelian_not_hasExt`: there is a large abelian category whose
  `Ext`-groups are not small.

## Implementation notes

The source's phrase "proper class" is expressed relative to a universe. The category has its
objects one universe above its (set-sized) morphisms, while failure of `HasExt.{u}` says that
its derived `Ext` morphisms cannot all be represented by types in `Type u`. Injectivity of
`α ↦ extensionClass α` is read off from the characterization of the `Ext`-class of a short
exact sequence, which turns equality of classes into an isomorphism of extensions compatible
with the inclusion, and such an isomorphism forces the shear to kill the inclusion.

## References

* [Stacks Project, Tag 07JT](https://stacks.math.columbia.edu/tag/07JT)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.Examples

open CategoryTheory.Limits

/-- The category structure on abelian groups, with the universe arguments pinned so that the
objects of `FreydRep` live one universe above its morphisms. -/
local instance addCommGrpCategory : Category.{u, u + 1} AddCommGrpCat.{u} :=
  AddCommGrpCat.instCategory

/-- The one-object category whose endomorphism monoid is the free monoid on the ordinals. -/
abbrev FreydBase : Type := SingleObj (FreeMonoid (Ordinal.{u}))

/-- Freyd's big abelian category: abelian-group-valued representations of the free monoid on
the ordinals. Its objects live one universe above its morphisms. -/
abbrev FreydRep : Type (u + 1) := FreydBase ⥤ AddCommGrpCat.{u}

private abbrev Zbig := ULift.{u, 0} ℤ

private abbrev AddCommGrpHom (X Y : AddCommGrpCat.{u}) :=
  @Quiver.Hom AddCommGrpCat addCommGrpCategory.toQuiver X Y

private def trivialEnd (X : AddCommGrpCat.{u}) : Ordinal.{u} → End X := fun _ => 0

private abbrev trivialRep (X : AddCommGrpCat.{u}) : FreydRep.{u} :=
  SingleObj.functor (FreeMonoid.lift (trivialEnd X))

private noncomputable def shear : End (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig) :=
  .of (biprod.snd ≫ biprod.inl)

private noncomputable def ordinalEnd (α : Ordinal.{u}) :
    Ordinal.{u} → End (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig) :=
  fun β => if β = α then shear else 0

private noncomputable abbrev extensionRep (α : Ordinal.{u}) : FreydRep.{u} :=
  SingleObj.functor (FreeMonoid.lift (ordinalEnd α))

private noncomputable def inclusionHom : AddCommGrpHom (AddCommGrpCat.of Zbig)
    (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig) := biprod.inl

private noncomputable def project : AddCommGrpHom (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig)
    (AddCommGrpCat.of Zbig) := biprod.snd

private lemma end_map_mul {M : Type*} [Monoid M] {D : Type v}
    [Category.{w, v} D] {Y : D} (f : M →* End Y) (x y : M) :
    (f (x * y)).asHom = (f y).asHom ≫ (f x).asHom := by
  rw [map_mul, End.mul_asHom]

/-- The action of a generator on the extension is the shear or zero. -/
private lemma extensionRep_map_of (α β : Ordinal.{u}) :
    (extensionRep α).map (X := SingleObj.star _) (Y := SingleObj.star _)
      (FreeMonoid.of β) = if β = α then shear.asHom else 0 := by
  change (ordinalEnd α β).asHom = _
  unfold ordinalEnd
  split_ifs <;> rfl

/-- Every generator acts by zero on the trivial representation. -/
private lemma trivialRep_map_of (β : Ordinal.{u}) :
    (trivialRep (AddCommGrpCat.of Zbig)).map (X := SingleObj.star _) (Y := SingleObj.star _)
      (FreeMonoid.of β) = 0 :=
  rfl

private lemma include_natural_generator (α β : Ordinal.{u}) :
    (trivialRep (AddCommGrpCat.of Zbig)).map (X := SingleObj.star _) (Y := SingleObj.star _)
        (FreeMonoid.of β) ≫ inclusionHom =
      inclusionHom ≫ (extensionRep α).map (X := SingleObj.star _) (Y := SingleObj.star _)
        (FreeMonoid.of β) := by
  rw [extensionRep_map_of, trivialRep_map_of]
  split_ifs
  · change (0 : AddCommGrpHom _ _) ≫ inclusionHom = inclusionHom ≫ shear.asHom
    simp [inclusionHom, shear]
  · change (0 : AddCommGrpHom _ _) ≫ inclusionHom = inclusionHom ≫ 0
    simp

private lemma project_natural_generator (α β : Ordinal.{u}) :
    (extensionRep α).map (X := SingleObj.star _) (Y := SingleObj.star _)
        (FreeMonoid.of β) ≫ project =
      project ≫ (trivialRep (AddCommGrpCat.of Zbig)).map (X := SingleObj.star _)
        (Y := SingleObj.star _) (FreeMonoid.of β) := by
  rw [extensionRep_map_of, trivialRep_map_of]
  split_ifs
  · change shear.asHom ≫ project = project ≫ (0 : AddCommGrpHom _ _)
    simp [project, shear]
  · change (0 : AddCommGrpHom _ _) ≫ project = project ≫ 0
    simp

private lemma natural_lift {X Y : AddCommGrpCat.{u}}
    (f : Ordinal.{u} → End X) (g : Ordinal.{u} → End Y) (i : AddCommGrpHom X Y)
    (h : ∀ β, ((FreeMonoid.lift f) (FreeMonoid.of β)).asHom ≫ i =
      i ≫ ((FreeMonoid.lift g) (FreeMonoid.of β)).asHom) :
    ∀ a, ((FreeMonoid.lift f) a).asHom ≫ i = i ≫ ((FreeMonoid.lift g) a).asHom := by
  intro a
  induction a using FreeMonoid.inductionOn with
  | one => simp
  | of β => exact h β
  | mul x y hx hy =>
      rw [end_map_mul (FreeMonoid.lift f) x y, end_map_mul (FreeMonoid.lift g) x y]
      simp only [Category.assoc]
      rw [hx, reassoc_of% hy]

private lemma nat_include (α : Ordinal.{u}) :
    ∀ a : FreeMonoid (Ordinal.{u}),
      (trivialRep (AddCommGrpCat.of Zbig)).map (X := SingleObj.star _)
          (Y := SingleObj.star _) a ≫ inclusionHom =
        inclusionHom ≫ (extensionRep α).map (X := SingleObj.star _)
          (Y := SingleObj.star _) a :=
  natural_lift _ _ _ (include_natural_generator α)

private lemma nat_project (α : Ordinal.{u}) :
    ∀ a : FreeMonoid (Ordinal.{u}),
      (extensionRep α).map (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ project =
        project ≫ (trivialRep (AddCommGrpCat.of Zbig)).map (X := SingleObj.star _)
          (Y := SingleObj.star _) a :=
  natural_lift _ _ _ (project_natural_generator α)

private noncomputable def includeNat (α : Ordinal.{u}) :
    trivialRep (AddCommGrpCat.of Zbig) ⟶ extensionRep α :=
  SingleObj.natTrans inclusionHom (nat_include α)

private noncomputable def projectNat (α : Ordinal.{u}) :
    extensionRep α ⟶ trivialRep (AddCommGrpCat.of Zbig) :=
  SingleObj.natTrans project (nat_project α)

private noncomputable def extensionShortComplex (α : Ordinal.{u}) : ShortComplex FreydRep :=
  ShortComplex.mk (includeNat α) (projectNat α) (by
    apply NatTrans.ext
    funext X
    cases X
    change biprod.inl ≫ biprod.snd = 0
    exact biprod.inl_snd)

private noncomputable def underlyingExtensionShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (biprod.inl : AddCommGrpCat.of Zbig ⟶
      AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig)
    (biprod.snd : AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig ⟶ AddCommGrpCat.of Zbig)
    (biprod.inl_snd)

private lemma underlyingExtensionShortExact :
    underlyingExtensionShortComplex.ShortExact := by
  simpa [underlyingExtensionShortComplex] using
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      (X₁ := AddCommGrpCat.of Zbig) (X₂ := AddCommGrpCat.of Zbig)).shortExact

private lemma extensionShortComplex_shortExact (α : Ordinal.{u}) :
    (extensionShortComplex α).ShortExact := by
  let ev := (evaluation FreydBase AddCommGrpCat).obj (SingleObj.star (FreeMonoid (Ordinal.{u})))
  let : ev.Faithful := {
    map_injective := by
      intro F G f g h
      apply NatTrans.ext
      funext X
      cases X
      exact h }
  have heval : (extensionShortComplex α).map ev = underlyingExtensionShortComplex := by
    dsimp [extensionShortComplex, underlyingExtensionShortComplex, ShortComplex.map,
      includeNat, projectNat, SingleObj.natTrans, ev]
    rfl
  apply (ShortExact.shortExact_map_iff ev).1
  rw [heval]
  exact underlyingExtensionShortExact

private lemma inclusionHom_ne_zero : inclusionHom ≠ 0 := by
  intro h
  have hid : (𝟙 (AddCommGrpCat.of Zbig) : AddCommGrpCat.of Zbig ⟶ _) = 0 := by
    calc
      𝟙 (AddCommGrpCat.of Zbig) = inclusionHom ≫ biprod.fst := by
        simp [inclusionHom]
      _ = 0 := by rw [h]; simp
  have hval := congrArg (fun f : AddCommGrpCat.of Zbig ⟶ AddCommGrpCat.of Zbig => f ⟨1⟩) hid
  have hfalse : (1 : ℤ) = 0 := by
    have h' : (⟨1⟩ : Zbig) = 0 := by simpa using hval
    exact congrArg ULift.down h'
  norm_num at hfalse

private lemma no_iso_extensions_of_ne {α β : Ordinal.{u}} (h : α ≠ β)
    (φ : extensionRep α ≅ extensionRep β)
    (hinc : includeNat α ≫ φ.hom = includeNat β) : False := by
  let ψ : AddCommGrpHom (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig)
      (AddCommGrpCat.of Zbig ⊞ AddCommGrpCat.of Zbig) :=
    φ.hom.app (SingleObj.star (FreeMonoid (Ordinal.{u})))
  have hincApp : inclusionHom ≫ ψ = inclusionHom := NatTrans.congr_app hinc _
  have hnatApp : shear.asHom ≫ ψ = ψ ≫ 0 := by
    have hnat := φ.hom.naturality (X := SingleObj.star _) (Y := SingleObj.star _)
      (FreeMonoid.of α)
    simp only [extensionRep_map_of, ↓reduceIte, h] at hnat
    exact hnat
  have hcross : inclusionHom = biprod.inr ≫ shear.asHom := by
    simp [inclusionHom, shear]
  refine inclusionHom_ne_zero ?_
  calc
    inclusionHom = inclusionHom ≫ ψ := hincApp.symm
    _ = (biprod.inr ≫ shear.asHom) ≫ ψ := by rw [hcross]
    _ = biprod.inr ≫ (ψ ≫ 0) := by rw [Category.assoc, hnatApp]
    _ = 0 := by simp

private noncomputable def extensionClass [HasExt.{u} FreydRep.{u}] (α : Ordinal.{u}) :
    Abelian.Ext.{u} (trivialRep (AddCommGrpCat.of Zbig))
      (trivialRep (AddCommGrpCat.of Zbig)) 1 :=
  (extensionShortComplex_shortExact α).extClass

private lemma extensionClass_injective [hExt : HasExt.{u} FreydRep.{u}] :
    Function.Injective extensionClass := by
  intro α β hclass
  obtain ⟨φ, hinc, -⟩ := ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum FreydRep
      (trivialRep (AddCommGrpCat.of Zbig)) (trivialRep (AddCommGrpCat.of Zbig))).2.1 _ _
      (includeNat α) (projectNat α) (extensionShortComplex α).zero
      (includeNat β) (projectNat β) (extensionShortComplex β).zero
      (extensionShortComplex_shortExact α) (extensionShortComplex_shortExact β)).1 hclass
  by_contra hne
  exact no_iso_extensions_of_ne hne φ hinc

private lemma not_small_extensionExt [hExt : HasExt.{u} FreydRep.{u}] :
    ¬ Small.{u} (Abelian.Ext.{u} (trivialRep (AddCommGrpCat.of Zbig))
      (trivialRep (AddCommGrpCat.of Zbig)) 1) :=
  fun _ => not_small_ordinal (small_of_injective extensionClass_injective)

/-- **Stacks 07JT.** There exists a large abelian category whose `Ext`-groups are not small
in the next lower universe. -/
@[stacks 07JT]
theorem exists_abelian_not_hasExt :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C) (_ : Abelian C),
      ¬ HasExt.{u} C := by
  refine ⟨FreydRep.{u}, inferInstance, inferInstance, fun _ => ?_⟩
  exact not_small_extensionExt inferInstance

end Stacks.Examples
