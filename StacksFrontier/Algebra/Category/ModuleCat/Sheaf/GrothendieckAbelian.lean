module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of modules are Grothendieck abelian, with independent universes

Mathlib proves that `SheafOfModules.{u} R` is a Grothendieck abelian category only when the
site, the sheaf of rings and the modules all live in the same universe `u`
(`SheafOfModules.instIsGrothendieckAbelian`).  Abelianness and exactness of filtered
colimits are already available with the three universes independent; what is missing is a
*separator*, because Mathlib's separating family for presheaves of modules is built from the
free presheaf of modules functor
`PresheafOfModules.free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`, whose construction
identifies the module universe with the ring universe.

This file supplies the missing separator, and hence the Grothendieck abelian structure and
enough injectives, with the module universe free to be larger than the site and ring
universes.

## Main results

* `Finsupp.mapDomainMapRange`: transport of finitely supported functions along a map of
  index types and a ring homomorphism; the universe-polymorphic ingredient that replaces
  `ModuleCat.free`.
* `PresheafOfModules.freeObjU`: the free presheaf of modules on a presheaf of types whose
  universe is independent of the universe of the sheaf of rings.
* `PresheafOfModules.freeYonedaU_isSeparating` and
  `PresheafOfModules.hasSeparatorU`: a separator for `PresheafOfModules.{max u r t} R`
  when the site is `u`-small and the rings are in universe `r`.
* `SheafOfModules.isGrothendieckAbelianU` and `SheafOfModules.enoughInjectivesU`:
  the Grothendieck abelian structure and enough injectives for
  `SheafOfModules.{max u r t} R`.
* `SheafOfModules.enoughInjectives_opens`: the same for a sheaf of rings on the site of
  opens of a topological space, which is the form needed by Čech-to-derived-functor
  spectral sequence data.

## Implementation notes

The free presheaf of modules on a presheaf of types `F : Cᵒᵖ ⥤ Type t`, over a presheaf of
rings `R : Cᵒᵖ ⥤ RingCat.{r}`, has sections `F.obj X →₀ R.obj X` and so lives in the module
universe `max r t`; nothing forces `t = r`.  The construction is carried out one level down,
as a presheaf of abelian groups together with pointwise module structures, and promoted by
`PresheafOfModules.ofPresheaf`; this avoids writing restriction-of-scalars coherences by
hand.  Every statement about the resulting object is proved by first restating the goal at
the level of `Finsupp` (where no categorical coercion intervenes) and then computing there.

The generators are the free presheaves of modules on the universe-lifted Yoneda presheaves
`yoneda.obj X ⋙ uliftFunctor`; the lift is what makes the family available in a module
universe larger than the site's.  They are separating because a map out of the generator at
`X` may send the tautological generating section to any prescribed section over `X`.

Because the module universe appears as `max u r t`, universe unification cannot infer `t`
from a goal; the results are therefore stated as theorems to be applied with explicit
universe arguments, in the order `t`, `u`, `r`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)
-/

@[expose] public section

universe t u r

open CategoryTheory Limits Opposite

namespace Finsupp

variable {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) {ι κ : Type*} (g : ι → κ)

/-- Transport of finitely supported functions along a map `g` of index types and a ring
homomorphism `φ` acting on the coefficients.  Unlike the free module functor
`ModuleCat.free`, this makes no universe assumption relating the index types to the rings. -/
@[ega "IV 11.2.2.2"]
noncomputable def mapDomainMapRange : (ι →₀ A) →+ (κ →₀ B) :=
  (Finsupp.mapDomain.addMonoidHom g).comp (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom)

/-- The transport of a single generator. -/
@[simp]
lemma mapDomainMapRange_single (i : ι) (c : A) :
    mapDomainMapRange φ g (Finsupp.single i c) = Finsupp.single (g i) (φ c) := by
  simp [mapDomainMapRange]

/-- Transport is semilinear along `φ`. -/
lemma mapDomainMapRange_smul (r : A) (a : ι →₀ A) :
    mapDomainMapRange φ g (r • a) = φ r • mapDomainMapRange φ g a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | single i c => simp [Finsupp.smul_single, map_mul]

/-- Transport along the identity is the identity. -/
lemma mapDomainMapRange_id : mapDomainMapRange (RingHom.id A) (id : ι → ι) = .id _ := by
  apply Finsupp.addHom_ext
  intro i c
  simp

variable {D : Type*} [Ring D] (ψ : B →+* D) {μ : Type*} (h : κ → μ)

/-- Transport is compatible with composition. -/
lemma mapDomainMapRange_comp :
    (mapDomainMapRange ψ h).comp (mapDomainMapRange φ g) =
      mapDomainMapRange (ψ.comp φ) (h ∘ g) := by
  apply Finsupp.addHom_ext
  intro i c
  simp

end Finsupp

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{r})

/-- The presheaf of abelian groups sending `X` to the free `R.obj X`-module on `F.obj X`.
The module universe `max r t` is independent of the universe `r` of the rings. -/
noncomputable def freeAbPresheafU (F : Cᵒᵖ ⥤ Type t) : Cᵒᵖ ⥤ AddCommGrpCat.{max r t} where
  obj X := AddCommGrpCat.of (F.obj X →₀ R.obj X)
  map {X Y} f := AddCommGrpCat.ofHom (Finsupp.mapDomainMapRange (R.map f).hom (F.map f))
  map_id X := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext'
    intro i
    apply AddMonoidHom.ext
    intro c
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext'
    intro i
    apply AddMonoidHom.ext
    intro c
    simp

variable {R}

/-- The restriction maps of `freeAbPresheafU`, read as transports of finitely supported
functions. -/
lemma freeAbPresheafU_map_apply {F : Cᵒᵖ ⥤ Type t} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : F.obj X →₀ R.obj X) :
    (freeAbPresheafU R F).map f a =
      Finsupp.mapDomainMapRange (R.map f).hom (F.map f) a := rfl

/-- The restriction maps of `freeAbPresheafU` on a generator. -/
lemma freeAbPresheafU_map_single {F : Cᵒᵖ ⥤ Type t} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : F.obj X) (c : R.obj X) :
    (freeAbPresheafU R F).map f (Finsupp.single i c) =
      Finsupp.single (F.map f i) (R.map f c) :=
  Finsupp.mapDomainMapRange_single (R.map f).hom (F.map f) i c

/-- The sections of `freeAbPresheafU` over `X` are a module over `R.obj X`. -/
noncomputable instance (F : Cᵒᵖ ⥤ Type t) (X : Cᵒᵖ) :
    Module (R.obj X) ((freeAbPresheafU R F).obj X) :=
  inferInstanceAs (Module (R.obj X) (F.obj X →₀ R.obj X))

variable (R) in
/-- The free presheaf of modules on a presheaf of types `F : Cᵒᵖ ⥤ Type t`, over a presheaf
of rings in universe `r`.  This is the universe-polymorphic form of
`PresheafOfModules.freeObj`, which requires `t = r`. -/
noncomputable def freeObjU (F : Cᵒᵖ ⥤ Type t) : PresheafOfModules.{max r t} R :=
  ofPresheaf (freeAbPresheafU R F)
    (fun {_ _} f r m ↦ Finsupp.mapDomainMapRange_smul (R.map f).hom (F.map f) r m)

section Desc

variable {F : Cᵒᵖ ⥤ Type t} {M : PresheafOfModules.{max r t} R}
  (φ : ∀ X, F.obj X → M.obj X)
  (hφ : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (i : F.obj X), φ Y (F.map f i) = M.map f (φ X i))

/-- The morphism of presheaves of abelian groups out of `freeAbPresheafU R F` determined by
a natural family of maps `F.obj X → M.obj X`. -/
noncomputable def freeAbDescU : freeAbPresheafU R F ⟶ M.presheaf where
  app X := AddCommGrpCat.ofHom
    (Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X)).toAddMonoidHom
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i c
    change Finsupp.lift (M.obj Y) (R.obj Y) (F.obj Y) (φ Y)
          (Finsupp.mapDomainMapRange (R.map f).hom (F.map f) (Finsupp.single i c)) =
        M.map f (Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) (Finsupp.single i c))
    rw [Finsupp.mapDomainMapRange_single, Finsupp.lift_apply, Finsupp.lift_apply,
      Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
      hφ f i, M.map_smul]
    rfl

/-- The morphism of presheaves of modules out of `freeObjU R F` determined by a natural
family of maps `F.obj X → M.obj X`. -/
noncomputable def freeObjDescU : freeObjU R F ⟶ M :=
  homMk (freeAbDescU φ hφ) (fun X r m ↦ by
    change Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) (r • m) =
      r • Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) m
    exact map_smul _ r m)

/-- The value of `freeObjDescU` on a generator. -/
lemma freeObjDescU_app_single (X : Cᵒᵖ) (i : F.obj X) (c : R.obj X) :
    (freeObjDescU φ hφ).app X (Finsupp.single i c) = c • φ X i := by
  change Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) (Finsupp.single i c) = c • φ X i
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

end Desc

section Separator

variable (R)

/-- The free presheaf of modules on the universe-lifted Yoneda presheaf at `X`.  The lift is
what makes this object available in the module universe `max u r t`, which may be strictly
larger than the universes of the site and of the rings. -/
noncomputable def freeYonedaU (X : C) : PresheafOfModules.{max u r t} R :=
  freeObjU R (yoneda.obj X ⋙ uliftFunctor.{t})

/-- **Every section of a presheaf of modules is in the image of a map from a generator.**
The map is the one sending the tautological generating section over `X` to the given
section. -/
lemma exists_freeYonedaU_hom {M : PresheafOfModules.{max u r t} R} (X : Cᵒᵖ) (x : M.obj X) :
    ∃ h : freeYonedaU.{t} R X.unop ⟶ M,
      h.app X (Finsupp.single (ULift.up (𝟙 X.unop)) 1) = x := by
  refine ⟨freeObjDescU (fun Y g ↦ M.restrictₛₗ g.down.op x) (fun {Y Z} f g ↦ ?_), ?_⟩
  · change M.map ((f.unop ≫ g.down).op) x = M.map f (M.map g.down.op x)
    rw [← M.map_comp_apply]
    rfl
  · refine (freeObjDescU_app_single _ _ X _ 1).trans ?_
    rw [one_smul]
    change M.map (𝟙 X) x = x
    rw [M.map_id]
    simp
    rfl

/-- **The free presheaves of modules on the universe-lifted Yoneda presheaves are a
separating family**, in any module universe containing those of the site and of the rings. -/
lemma freeYonedaU_isSeparating :
    ObjectProperty.IsSeparating (.ofObj (freeYonedaU.{t} R)) := by
  intro M N f₁ f₂ h
  ext X x
  obtain ⟨g, hg⟩ := exists_freeYonedaU_hom.{t} R X x
  have hcomp := h _ ⟨X.unop⟩ g
  have e2 : (g.app X ≫ f₁.app X) (Finsupp.single (ULift.up (𝟙 X.unop)) 1) =
      (g.app X ≫ f₂.app X) (Finsupp.single (ULift.up (𝟙 X.unop)) 1) := by
    rw [← comp_app, ← comp_app, hcomp]
  rw [← hg]
  exact e2

/-- The separating family is indexed by the objects of the site, hence small. -/
instance : ObjectProperty.Small.{u} (.ofObj (freeYonedaU.{t} R)) := by
  infer_instance

/-- **Presheaves of modules over a presheaf of rings on a small site have a separator**, in
any module universe containing those of the site and of the rings. -/
theorem hasSeparatorU [HasColimitsOfShape (Discrete C) AddCommGrpCat.{max u r t}] :
    HasSeparator (PresheafOfModules.{max u r t} R) :=
  ⟨_, (freeYonedaU_isSeparating.{t} R).isSeparator_coproduct⟩

end Separator

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{max u r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r t}]

/-- **Sheaves of modules over a sheaf of rings on a small site have a separator**, in any
module universe containing those of the site and of the rings: the separator of presheaves
of modules is carried across the sheafification adjunction. -/
theorem hasSeparatorU : HasSeparator (SheafOfModules.{max u r t} R) :=
  have : HasSeparator (PresheafOfModules.{max u r t} R.obj) :=
    PresheafOfModules.hasSeparatorU.{t, u, r} R.obj
  HasSeparator.of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

/-- **Sheaves of modules over a sheaf of rings on a small site form a Grothendieck abelian
category**, with the site, ring and module universes independent.  Mathlib's
`SheafOfModules.instIsGrothendieckAbelian` requires all three to agree; abelianness and
exactness of filtered colimits are already universe-independent, and the separator is what
this generalizes. -/
theorem isGrothendieckAbelianU :
    IsGrothendieckAbelian.{max u r t} (SheafOfModules.{max u r t} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules R
  hasSeparator := hasSeparatorU.{t, u, r} R

/-- **Sheaves of modules over a sheaf of rings on a small site have enough injectives**,
with the site, ring and module universes independent. -/
theorem enoughInjectivesU : EnoughInjectives (SheafOfModules.{max u r t} R) :=
  have := isGrothendieckAbelianU.{t, u, r} R
  inferInstance

end SheafOfModules

namespace SheafOfModules

variable (X : Type u) [TopologicalSpace X]

/-- Sheafification of abelian presheaves on the site of opens of a topological space exists
in any coefficient universe containing that of the space: the site is small there, hence
essentially small. -/
theorem hasSheafify_opens :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u t} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _

/-- On the site of opens of a topological space, the maps of abelian presheaves inverted by
sheafification are exactly the locally bijective ones, in any coefficient universe
containing that of the space. -/
theorem wEqualsLocallyBijective_opens :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u t} _

/-- **Sheaves of modules on a topological space have enough injectives**, with the space,
ring and module universes independent.  This is the hypothesis asked for by
Čech-to-derived-functor spectral sequence data on a ringed space. -/
@[sga "4½ Etat_0 6.2" "special case"]
theorem enoughInjectives_opens
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r}) :
    EnoughInjectives (SheafOfModules.{max u r t} O) := by
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r t} :=
    hasSheafify_opens.{max r t, u} X
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u r t} :=
    wEqualsLocallyBijective_opens.{max r t, u} X
  exact enoughInjectivesU.{t, u, r} O

end SheafOfModules

end
