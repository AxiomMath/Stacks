module

public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Local surjectivity of sheafification for presheaves of modules

Let `J` be a Grothendieck topology on `C` and `R` a ring. The sheafification unit
`P ⟶ P^#` of a presheaf of `R`-modules is locally surjective: every section of `P^#` is, on a
covering, in the image of a section of `P`.

The argument is the one used for abelian groups in
`StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives`, and it is carried out
here for modules for the same reason: it assumes no relation between the carrier universe `w`
and the universes of the site. Mathlib's
`CategoryTheory.Presheaf.isLocallySurjective_toSheafify'` needs the carrier universe to be
`max u v`, and the route through
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` needs that hypothesis, which for
`ModuleCat.{w} R` is again only available at `w = max u v`.

**There is no size hypothesis at all.** A hypothesis
`UnivLE.{max u v, w}` would enter at exactly one point: the sheaf condition for the underlying
presheaf of *sets* of a sheaf of modules, i.e.
`CategoryTheory.GrothendieckTopology.HasSheafCompose` for the forgetful functor to types. That
instance is genuinely unavailable at a free `w` — the forgetful functor of `ModuleCat.{w} R` is
corepresented by `R` itself, which does not live in `Type w` unless `R` does, in contrast with
`AddCommGrpCat.{w}`, whose forgetful functor is corepresented by `ULift ℤ` for every `w`. It is
also not needed: the sheaf condition for a module-valued presheaf is, by definition, the sheaf
condition for each of the presheaves of types corepresented by a module, and the argument below is
carried out there.

The sections of `Q` which are locally in the image of `φ : P ⟶ Q` form a submodule of `Q X` in
each degree: the set is closed under addition and negation as in the abelian case, and under
`r • -` because a local lift `a` of `s` gives the local lift `r • a` of `r • s`. The resulting
subpresheaf is a sheaf whenever `Q` is, and that is the step where the universes would enter.
What replaces the passage to sets: for a module `E`, the maps `E ⟶ Q X` all of whose values are
locally in the image form a `CategoryTheory.Subfunctor` of the presheaf of types corepresented by
`E`, and that subfunctor satisfies `CategoryTheory.Subfunctor.isSheaf_iff` because the defining
sieve pulls back (`CategoryTheory.Presheaf.pullback_imageSieve`) and the topology is transitive.
The sheafification unit then factors through the subpresheaf of modules and the factorization
splits its inclusion, which says exactly that every section is locally in the image.

## Main results

* `Stacks.Sheafification.isLocallySurjective_toSheafify_moduleCat` — the sheafification unit of
  a presheaf of `R`-modules is locally surjective, with no relation assumed between the carrier
  universe and the site.

## References

* [Stacks Project, Tag 00WK](https://stacks.math.columbia.edu/tag/00WK)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.GrothendieckTopology hiding sheafify toSheafify
open Opposite

namespace Stacks.Sheafification

universe w r v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type r} [Ring R]

/-- A section which is locally in the image of `φ` stays so after restriction. -/
private lemma imageSieve_map_mem {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) {s : Q.obj X} (hs : Presheaf.imageSieve φ s ∈ J X.unop) :
    Presheaf.imageSieve φ (Q.map f s) ∈ J Y.unop := by
  rw [← Presheaf.pullback_imageSieve]
  exact J.pullback_stable f.unop hs

/-- Every image of `φ` is locally in the image of `φ`. -/
private lemma imageSieve_app_mem {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) {X : Cᵒᵖ}
    (p : P.obj X) : Presheaf.imageSieve φ (φ.app X p) ∈ J X.unop := by
  rw [Presheaf.imageSieve_app]
  exact J.top_mem _

/-- The sections of `Q` which are locally in the image of `φ : P ⟶ Q` form a submodule in each
degree. -/
private def localImageSubmodule {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) (X : Cᵒᵖ) :
    Submodule R (Q.obj X) where
  carrier := {s | Presheaf.imageSieve φ s ∈ J X.unop}
  zero_mem' := by
    change Presheaf.imageSieve φ (0 : Q.obj X) ∈ J X.unop
    rw [show (0 : Q.obj X) = φ.app X 0 from (map_zero _).symm]
    exact imageSieve_app_mem J φ _
  add_mem' := by
    intro s t hs ht
    apply J.superset_covering _ (J.intersection_covering hs ht)
    rintro Y f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  smul_mem' := by
    intro r s hs
    apply J.superset_covering _ hs
    rintro Y f ⟨a, ha⟩
    exact ⟨r • a, by simp only [map_smul, ha]⟩

/-- The subpresheaf of sections locally in the image of `φ : P ⟶ Q`. -/
private def localImageModule {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) :
    Cᵒᵖ ⥤ ModuleCat.{w} R where
  obj X := ModuleCat.of R (localImageSubmodule J φ X)
  map {X Y} f := ModuleCat.ofHom
    ((Q.map f).hom.restrict (p := localImageSubmodule J φ X) (q := localImageSubmodule J φ Y) (by
      intro s hs
      exact imageSieve_map_mem J φ f hs))
  map_id X := by
    ext x
    change Q.map (𝟙 X) x.val = x.val
    simp
  map_comp f g := by
    ext x
    change Q.map (f ≫ g) x.val = Q.map g (Q.map f x.val)
    simp

/-- The inclusion of the subpresheaf of sections locally in the image. -/
private def localImageModuleι {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) :
    localImageModule J φ ⟶ Q where
  app X := ModuleCat.ofHom (localImageSubmodule J φ X).subtype

/-- The factorization of `φ` through the sections locally in its image. -/
private def toLocalImageModule {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) :
    P ⟶ localImageModule J φ where
  app X := ModuleCat.ofHom ((φ.app X).hom.codRestrict (localImageSubmodule J φ X) (by
    intro s
    exact imageSieve_app_mem J φ s))
  naturality X Y f := by
    ext s
    exact Subtype.ext (NatTrans.naturality_apply φ f s)

/-- The sections locally in the image of `φ`, read as a subfunctor of the presheaf of types
corepresented by a module `E`: a map `E ⟶ Q X` belongs to it when every value is locally in the
image. This is the same condition as `Stacks.Sheafification.localImageSubmodule`, phrased for the
presheaves of types out of which the sheaf condition for module-valued presheaves is built. -/
private lemma coyoneda_comp_map_apply {Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (E : ModuleCat.{w} R)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) (g : (Q ⋙ coyoneda.obj (op E)).obj X) (e : E) :
    ConcreteCategory.hom (ConcreteCategory.hom ((Q ⋙ coyoneda.obj (op E)).map i) g) e =
      Q.map i (ConcreteCategory.hom g e) := rfl

private def localImageSubfunctor {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q)
    (E : ModuleCat.{w} R) : Subfunctor (Q ⋙ coyoneda.obj (op E)) where
  obj X := {g : E ⟶ Q.obj X | ∀ e : E, Presheaf.imageSieve φ (g e) ∈ J X.unop}
  map {X Y} i g hg := fun e => by
    rw [coyoneda_comp_map_apply]
    exact imageSieve_map_mem J φ i (hg e)

/-- The subfunctor of sections locally in the image is a sheaf of types whenever `Q` is a sheaf of
modules. Local character of the covering condition is the whole content: by
`CategoryTheory.Presheaf.pullback_imageSieve` the defining sieve pulls back, so a section which
lies in the subfunctor on a covering already lies in it. -/
private lemma localImageSubfunctor_isSheaf {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) (E : ModuleCat.{w} R) :
    Presieve.IsSheaf J (localImageSubfunctor J φ E).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (hQ E)]
  intro X g hg e
  refine J.transitive hg _ fun {Y} i hi => ?_
  have h2 := hi e
  rwa [coyoneda_comp_map_apply, ← Presheaf.pullback_imageSieve] at h2

/-- A module map into the submodule of sections locally in the image is the same thing as a module
map into the ambient module all of whose values are locally in the image. -/
private def localImageModuleCoyonedaEquiv {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q)
    (E : ModuleCat.{w} R) (X : Cᵒᵖ) :
    (E ⟶ (localImageModule J φ).obj X) ≃
      {g : E ⟶ Q.obj X // ∀ e : E, Presheaf.imageSieve φ (g e) ∈ J X.unop} where
  toFun h := ⟨h ≫ (localImageModuleι J φ).app X, fun e => (h e).property⟩
  invFun g := ModuleCat.ofHom (g.val.hom.codRestrict (localImageSubmodule J φ X) g.property)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The presheaf of types corepresented by `E` out of the subpresheaf of modules of sections
locally in the image is the subfunctor `Stacks.Sheafification.localImageSubfunctor`. -/
private def localImageModuleCoyonedaIso {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q)
    (E : ModuleCat.{w} R) :
    localImageModule J φ ⋙ coyoneda.obj (op E) ≅ (localImageSubfunctor J φ E).toFunctor :=
  NatIso.ofComponents (fun X => Equiv.toIso (localImageModuleCoyonedaEquiv J φ E X))
    (fun {X Y} i => by
      ext h
      exact Subtype.ext rfl)

/-- The subpresheaf of sections locally in the image is a sheaf of modules whenever `Q` is, with
no relation assumed between the carrier universe and the universes of the site: the argument is
carried out at the level of the presheaves of types corepresented by the modules, out of which the
sheaf condition for a module-valued presheaf is built, and never passes to the underlying presheaf
of sets. -/
private lemma localImageModule_isSheaf {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) : Presheaf.IsSheaf J (localImageModule J φ) := fun E =>
  Presieve.isSheaf_iso J (localImageModuleCoyonedaIso J φ E).symm
    (localImageSubfunctor_isSheaf J φ hQ E)

/-- **Sheafification of presheaves of modules is locally surjective**, independently of the
universe of the underlying modules. -/
instance isLocallySurjective_toSheafify_moduleCat [HasWeakSheafify J (ModuleCat.{w} R)]
    (P : Cᵒᵖ ⥤ ModuleCat.{w} R) : Presheaf.IsLocallySurjective J (toSheafify J P) where
  imageSieve_mem {U} s := by
    let φ := toSheafify J P
    have hP := ((presheafToSheaf J (ModuleCat.{w} R)).obj P).property
    have hS : Presheaf.IsSheaf J (localImageModule J φ) := localImageModule_isSheaf J φ hP
    let l := CategoryTheory.sheafifyLift J (toLocalImageModule J φ) hS
    have hl : l ≫ localImageModuleι J φ = 𝟙 _ := by
      refine CategoryTheory.sheafify_hom_ext J _ _ hP ?_
      rw [← Category.assoc, CategoryTheory.toSheafify_sheafifyLift]
      ext X x
      rfl
    have hs := (l.app (op U) s).property
    have he : (l.app (op U) s).val = s :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hl (op U)) s
    change Presheaf.imageSieve φ s ∈ J U
    rwa [he] at hs

end Stacks.Sheafification

end
